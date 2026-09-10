# =============================================================================
#  sketch_wt.py  --  AMYBOARD ADVANCED WAVETABLE SYNTH v1
#  4-voice / 8-oscillator MicroPython wavetable synth for AMYboard (AMY engine)
# =============================================================================
#
#  ARCHITECTURE (per voice -- 5 AMY oscillators, 4 voices = 20 oscs, 8 sounding)
#
#      HEAD (SILENT)  <- filter + filter drive + voice pan + MOD4 envelope
#        |  chained_osc
#      OSC A (WAVETABLE)  -- position/pitch/level/drive, amp EG, MOD3 envelope
#        |  chained_osc
#      OSC B (WAVETABLE)  -- ditto
#
#      MOD1 osc (silent)  \  mod_source of HEAD / A / B  -> mod0 coefficient
#      MOD2 osc (silent)  /                              -> mod1 coefficient
#
#  Each of the four voices is its OWN AMY synth (WT_SYNTH0..+3), not four
#  voices of one synth.  This is deliberate and load-bearing -- see the
#  "WHY FOUR SYNTHS" note below.  It is what makes per-voice unison detune and
#  per-voice stereo spread possible at all, and it lets MONO / UNISON / POLY be
#  three allocation policies over one fixed set of AMY objects, so switching
#  mode allocates nothing and cuts no notes.
#
#  RULES INHERITED FROM THE MEGATRON (sketch_va8) BUILD -- DO NOT REGRESS:
#    * amy.reset() at boot and on PANIC only.  Never on a parameter change.
#    * vel=0 is note-off.
#    * Bus 0 is always audible.
#    * MIDI via midi.add_callback() -- never tulip.midi_callback(), which
#      replaces the system dispatcher and breaks everything else.
#    * A SOUNDING chain head filters ONLY ITSELF.  Only a wave=SILENT head is
#      processed AFTER the chain is summed, so a voice-wide filter REQUIRES a
#      silent head.  (src/amy.c render_osc_wave / render_envelope order.)
#    * Per-osc `note` DOES NOT WORK inside a chain -- chained oscs are role
#      SYNTH_IS_CHAINED and refuse notes.  All pitch offsets live in each osc's
#      `freq` COEFFICIENT (const in Hz against REF_HZ, note coef 1).
#    * `phase=` warps the RUNNING phase as well as setting the retrigger phase,
#      so it is only ever sent on a full (re)build, never on a knob turn.
#    * The head's amp must NOT carry an envelope: render_envelope() runs on the
#      SUMMED chain for a SILENT osc, which would put a second VCA over the
#      whole voice on top of each oscillator's own.
#    * Display colours are 0..15 (framebuf GS4_HMSB low nibble), not 0..255.
#    * OLED is an SH1107 at 0x3D; amyboard's autodetect binds the SSD1327
#      driver to it and paints noise, so init_display() forces the driver.
#
#  VERIFIED AGAINST THE AMY SOURCE (shorepine/amy), not guessed -- see the
#  "AMY CAPABILITY NOTES" block below for what is and is not available, and
#  what each unavailable feature was replaced with.
# =============================================================================

import amy
import tulip
import time
import math
import json
import array
import os
import struct

try:
    import amyboard
    HAVE_BOARD = True
except Exception:
    HAVE_BOARD = False

try:
    import midi as midimod
    HAVE_MIDI = True
except Exception:
    HAVE_MIDI = False


def clamp(v, lo, hi):
    if v < lo:
        return lo
    if v > hi:
        return hi
    return v


# --------------------------------------------------------------------------
#  RESILIENT AMY SEND  --  survive version skew between AMY builds
# --------------------------------------------------------------------------
#  The AMY on the web REPL, the AMYboard firmware and the desktop package are
#  built from different snapshots, so a keyword one build knows another may
#  reject outright: amy.message() raises "Unknown keyword X" the moment it sees
#  one it does not have, and that aborts the WHOLE message.  That is exactly how
#  a single unsupported `dist_clip` used to take the entire OSC A/B setup down
#  with it -- leaving the oscillators as plain default sines, which is why
#  changing the wavetable or its position "did nothing".
#
#  _amy_send() makes one unknown keyword cost only that keyword: it drops the
#  rejected key and retries, so the wavetable, filter, envelopes and everything
#  else in the same message still get through.  Each missing keyword is
#  reported once.  The fast path (all keywords known) adds nothing but a
#  try/except that never fires.
_amy_unknown_kw = set()


def _amy_send(**kw):
    try:
        amy.send(**kw)
        return
    except ValueError as e:
        if "Unknown keyword" not in str(e):
            raise
    # Slow path: strip whatever this build does not understand, then retry.
    while kw:
        try:
            amy.send(**kw)
            return
        except ValueError as e:
            msg = str(e)
            if "Unknown keyword" not in msg:
                raise
            bad = msg.rsplit(" ", 1)[-1].strip()
            if bad not in kw:
                print("amy: rejected send could not be repaired:", msg)
                return
            del kw[bad]
            if bad not in _amy_unknown_kw:
                _amy_unknown_kw.add(bad)
                print("amy: this build has no '%s' -- that feature is skipped"
                      % bad)


def _amy_knows(kw):
    """True if this AMY build accepts keyword `kw`.

    Reads amy._KW_MAP (the send() vocabulary) when it is exposed -- present on
    every build, just with different entries -- and falls back to a harmless
    message() probe (which only builds a wire string, never sends) otherwise."""
    m = getattr(amy, "_KW_MAP", None)
    if isinstance(m, dict):
        return kw in m
    try:
        amy.message(**{kw: 0})
        return True
    except Exception:
        return False


# Whether this AMY build has the per-osc / per-bus distortion block
# (dist_clip / dist_fold / dist_crush / dist_drive / dist_mix).  Probed once in
# boot(); assume present until then.  When False, the DRIVE/FOLD controls and
# the DRIVE FX page simply do nothing rather than crashing the voice build.
HAVE_DIST = True


# =============================================================================
#  AMY CAPABILITY NOTES  --  what the brief asked for vs what AMY actually has
# =============================================================================
#  Checked against src/amy.h, src/oscillators.c, src/pcm.c, amy/__init__.py's
#  _KW_MAP_LIST (the source of truth for send() kwargs) and docs/api.md.
#
#  AVAILABLE, USED AS ASKED
#    * wave=WAVETABLE (amy.h: 19).  A table is 256 samples per cycle; the cycle
#      count is sample_length >> 8, so 16384 samples is 64 cycles.  `duty`
#      crossfades across the cycles -- so WAVETABLE POSITION IS THE `duty`
#      CONTROL-COEFFICIENT LIST, which means position scanning is modulated
#      inside AMY's DSP by envelopes and LFOs at zero MicroPython cost.
#      (oscillators.c render_wavetable.)
#    * Custom wavetables from SD.  render_wavetable calls
#      pcm_get_sample_ram_for_preset(), and pcm.c's get_preset_for_preset_number
#      checks RAM/memory presets FIRST -- they shadow the baked-in ROM presets.
#      So amy.load_sample(path, preset=N) makes an SD .wav playable as
#      wave=WAVETABLE, preset=N.  This is the whole SD wavetable mechanism.
#      shorepine/amy#997 widened it: ANY PCM .wav of at least two 256-sample
#      cycles (>= 512 samples) is a valid wavetable now, not only purpose-built
#      64-cycle ones -- render_wavetable only requires sample_length >=
#      2*256 and derives the cycle count from the length -- so ordinary
#      one-shot samples can be scanned as wavetables too.  The synth ALWAYS
#      boots on its built-in tables and reads the card only on demand (the WT
#      LOAD page, or a patch that names an SD table); see wt_builtins() /
#      wt_scan_sd() and the STARTUP CONTRACT note in section 3.
#    * Per-osc filter: filter_type 0-6 = none / LP12 / BP / HP / LP24 / NOTCH /
#      PHASER, `resonance` 0.5-16, cutoff as a coefficient list (const Hz,
#      other terms in OCTAVES) so cutoff modulation is free.
#    * Two envelope generators per osc (bp0/eg0, bp1/eg1), up to 8 breakpoints,
#      four curve shapes (eg0_type/eg1_type).  All envelopes are AMY's own --
#      nothing is stepped from Python.
#    * Distortion per osc AND per bus: dist_clip, dist_fold (wavefolder),
#      dist_crush [bits,rate], dist_drive (coefs -> MODULATABLE), dist_mix.
#    * Bus FX: reverb, chorus, echo, eq, plus the distortion block above.
#    * portamento (ms) per osc, for MONO glide.
#
#  NOT AVAILABLE -- AND WHAT IS USED INSTEAD
#    * OSCILLATOR SYNC.  AMY has no hard sync of any kind (no sync_osc /
#      osc_sync anywhere in src/).  CLOSEST ALTERNATIVE, implemented: per-osc
#      `phase` retrigger (PH.SYNC on the MIX page) locks both wavetables to a
#      fixed start phase on every note-on, which gives the phase-coherent
#      attack transient sync is usually reached for.  A real sync sweep is not
#      possible without a C DSP slot.
#    * TRUE AUDIO-RATE FM / RING MOD BETWEEN TWO WAVETABLES.  AMY's audio-rate
#      FM engine is wave=ALGO, and docs/synth.md is explicit that ALGO operator
#      sources must be SINE -- it cannot take wavetable operators.  The general
#      `mod_source` path IS available to any wave, but it is evaluated once per
#      audio BLOCK (control rate, AMY_BLOCK_SIZE/AMY_SAMPLE_RATE), not per
#      sample.  IMPLEMENTED INSTEAD: MOD1/MOD2 have a RATE MODE -- as LFOs they
#      are ordinary low-frequency modulators, and switched to AUDIO they track
#      the played note by ratio and become FM/RM operators feeding the same
#      coefficient slots.  MOD->PITCH is then FM, MOD->LEVEL is ring-mod
#      flavour (log-domain, control-rate -- the aliased edge is characteristic,
#      not a clean sideband spectrum).  This costs nothing extra: MOD1/MOD2 are
#      silent mod oscs that already exist in every voice.
#      Routing OSC B directly into OSC A as a mod_source would also work, but
#      `mod_source` SILENCES the source oscillator -- it would cost the voice
#      its second wavetable.  The shared-operator design above keeps both
#      wavetables audible, which is what the brief actually wants.
#    * FILTER RESONANCE MODULATION.  `resonance` is a plain float ('RF' in
#      _KW_MAP_LIST), not a coefficient list, so nothing can modulate it inside
#      AMY.  RESO is a static per-patch control; the MATRIX shows it as
#      unavailable rather than pretending.
#    * MODULATING AN FX PARAMETER, or an FM AMOUNT, per note.  Bus FX are bus
#      scope -- they have no per-note modulation inputs at all (api.md is
#      explicit that at bus scope only the const term of a coef list is used).
#      An FM *amount* is itself a coefficient, and AMY cannot modulate a
#      coefficient.  There is no workaround inside AMY: FM depth is the
#      modulator's own amplitude, and a mod-source oscillator CANNOT carry an
#      envelope either -- src/amy.c's note-on and note-off handlers both skip
#      any osc whose role is SYNTH_IS_MOD_SOURCE (amy.c:1921 / :1983), so a mod
#      osc never sees a velocity event and its EGs never fire.  An FM amount is
#      therefore static per patch.  CLOSEST ALTERNATIVE, implemented: route
#      MOD3/MOD4 (real envelopes) to the carrier's PITCH or LEVEL alongside the
#      FM operator, which shapes how the FM reads across the note.  MOD1/MOD2
#      phase CAN still be retriggered per note (TRIG on each MOD page), because
#      `phase` is an ordinary parameter message, not a note event.
#    * A BIPOLAR ENVELOPE / UNIPOLAR LFO as such.  AMY envelopes run 0..1 and
#      an oscillator swings +/-1.  Both polarities are still provided, by
#      compensating the destination's CONST term against the routing depth
#      (see mod_terms()) -- exact for every linear/log destination.  Amplitude
#      is the documented exception: amp coefficients combine in the LOG domain
#      rather than adding, so amp routings are sent through un-compensated.
#
#  NOT VERIFIABLE FROM SOURCE ALONE -- CHECK ON YOUR BOARD
#    * `wave=WAVETABLE` is compiled in only with -DAMY_WAVETABLE.  It is on in
#      AMY's own Makefile and setup.py, but the AMYboard MicroPython firmware
#      is built out of the tulipcc tree, which this sketch cannot inspect.  If
#      your firmware lacks it, OSC A/B render silence.  Run wt_selftest() from
#      the REPL: it plays a note, reads AMY's own output buffer back and tells
#      you.  Set WT_ENABLED = False to fall back to SAW_DOWN oscillators and
#      keep every other feature (filter, envelopes, matrix, FX) working.
# =============================================================================

# --------------------------------------------------------------------------
#  SECTION 1 : CONFIGURATION
# --------------------------------------------------------------------------
SR = 44100          # AMYboard (ESP32-S3) AMY_SAMPLE_RATE
BUS = 0             # bus 0 is always audible
NVOICE = 4          # 4 voices, hard ceiling from the brief
WT_SYNTH0 = 1       # voices occupy synths 1..4
MUTE_VEL = 0.001

# ---- per-voice oscillator map (voice-relative osc numbers) ----------------
# mod_source / chained_osc are VOICE-RELATIVE inside a synth (docs/synth.md
# Note 3), so these indices are exactly what gets sent.
HEAD = 0            # SILENT: filter, filter drive, voice pan, MOD4 envelope
OSC_A = 1           # WAVETABLE
OSC_B = 2           # WAVETABLE
MOD1_OSC = 3        # silent mod source -> mod0 coefficient
MOD2_OSC = 4        # silent mod source -> mod1 coefficient
OSCS_PER_VOICE = 5

# AMY's logfreq reference (ZERO_LOGFREQ_IN_HZ in amy.h).  A freq coefficient
# const of REF_HZ * 2**(semitones/12) is exactly a semitone offset riding on
# top of whatever note the voice is playing.  const 0 is NOT "no offset" --
# it is ZERO_HZ_LOG_VAL, i.e. silence -- so this is never allowed to reach 0.
REF_HZ = 440.0

# The head is a unity pass-through and must carry NO envelope (see the rules
# block at the top).  Coefficients: const, note, vel, eg0.
HEAD_AMP_CONST = 1.0

# Waveform ids, read from the module where possible so a firmware renumber
# cannot silently break us.
W_SILENT = getattr(amy, "SILENT", 20)
W_WAVETABLE = getattr(amy, "WAVETABLE", 19)
W_SINE = getattr(amy, "SINE", 0)
W_PULSE = getattr(amy, "PULSE", 1)
W_SAW_DOWN = getattr(amy, "SAW_DOWN", 2)
W_SAW_UP = getattr(amy, "SAW_UP", 3)
W_TRIANGLE = getattr(amy, "TRIANGLE", 4)
W_NOISE = getattr(amy, "NOISE", 5)

# Set False if wt_selftest() says this firmware has no -DAMY_WAVETABLE.
# Everything else in the synth keeps working; the two oscillators just render
# a plain saw and the POSITION controls go inert.
WT_ENABLED = True
WT_FALLBACK_WAVE = W_SAW_DOWN

# Control-coefficient slot indices, from parse_ctrl_coefs()'s docstring:
#   0 const, 1 note, 2 vel, 3 eg0, 4 eg1, 5 mod0, 6 bend, 7 ext0, 8 ext1, 9 mod1
C_CONST, C_NOTE, C_VEL, C_EG0, C_EG1, C_MOD0, C_BEND = 0, 1, 2, 3, 4, 5, 6
C_EXT0, C_EXT1 = 7, 8       # external CV inputs 0/1 (AMY cv_in channels 0/1)
C_MOD1 = 9
NCOEF = 10

# Cutoff safety ceiling.  filter_freq coefficients combine in the LOG domain:
# the const is Hz but every other term adds OCTAVES, and AMY does not clamp the
# sum -- a resonant biquad driven past Nyquist goes unstable and rings at a
# fixed pitch on every note.  Inherited straight from the Megatron build.
FILT_CEILING = 15000.0


# --------------------------------------------------------------------------
#  EURORACK CV IN  --  CV1 = GATE, CV2 = 1V/oct PITCH
# --------------------------------------------------------------------------
#  Ported verbatim from the Megatron (megatron_v1) build, which is verified
#  working on this hardware.  The ONLY adaptations are structural: the note is
#  addressed to voice 0's SILENT head (this synth is four one-voice synths, not
#  one 8-osc voice), and the pitch CV rides the wavetable oscillators' `ext`
#  freq coefficient via osc_freq_coefs().  Everything else -- the gate edge
#  detector, the track/gate pitch paths, the by-ear calibration -- is the
#  Megatron's code.
#
#  Both paths run in AMY's AUDIO THREAD, never a Python loop() poll: the gate
#  is AMY's own C-side edge detector (cv_trigger), and TRACK-mode pitch is a
#  live term on the oscillator freq coefficient evaluated once per audio block.
CV_PITCH_MODE  = 'track'   # 'track' (continuous) or 'gate' (sample-at-gate)
CV_ENABLED     = True      # False leaves both CV jacks disconnected from audio
CV_GATE_INPUT  = 0         # CV1 jack: gate/trigger
CV_PITCH_INPUT = 1         # CV2 jack: 1V/oct pitch
CV_GATE_ON     = 2.5       # gate opens above this many volts...
CV_GATE_OFF    = 1.25      # ...and closes below this (hysteresis)
CV_GATE_VEL    = 1.0       # velocity (0..1) given to CV-gated notes
CV_BASE_NOTE   = 60        # MIDI note that 0V on the pitch jack sounds
CV_PITCH_TRIM_CENTS = 0.0  # + raises everything, - lowers (offset, cents)
CV_PITCH_SCALE      = 1.0  # octaves added per volt (1.0 = a true 1V/oct)
# AMY CV channel 0 is 'ext0' (coef index 7), channel 1 is 'ext1' (index 8).
CV_PITCH_COEF = C_EXT0 if CV_PITCH_INPUT == 0 else C_EXT1
CV_PITCH_COARSE_V = 0.0    # ATTEN knob (coarse volts of correction)
CV_PITCH_OFFSET_V = 0.0    # OFFSET knob (fine volts of correction)
CV_CAL_FILE = "/user/wt_cv_cal.json"
_cv_cal_msg = "offset by ear"


def cv_offset_volts():
    """Total correction ADDED to the incoming pitch CV, in volts."""
    return CV_PITCH_COARSE_V + CV_PITCH_OFFSET_V


def cv_const_mult():
    """Frequency multiplier carrying the CV offset, for the oscillator const.

    THIS is what makes OFFSET audible in 'track' mode: the correction cannot
    ride the ext coefficient (a pure multiplier, no offset term), so it folds
    into the per-oscillator const, on the path retune() re-pushes on every
    edit.  'gate' mode bakes the whole sum into the note instead, so it must
    NOT be applied here too (that would count it twice)."""
    if CV_ENABLED and CV_PITCH_MODE == 'track':
        return 2.0 ** (CV_PITCH_SCALE * cv_offset_volts())
    return 1.0


def cv_pitch_coefs():
    """(ext0, ext1) freq coefficients carrying the pitch jack, 'track' only.

    In 'gate' mode the pitch is baked into the note at the gate edge, so this
    MUST stay zero there or the CV is counted twice."""
    if not (CV_ENABLED and CV_PITCH_MODE == 'track'):
        return 0.0, 0.0
    return ((CV_PITCH_SCALE, 0.0) if CV_PITCH_COEF == C_EXT0
            else (0.0, CV_PITCH_SCALE))


def cv_base_note():
    """The note a RAW reading of 0V sounds, as a fractional MIDI note.

    Uncalibrated (offset 0, scale 1) this is just BASE + TRIM.  In 'gate' mode
    the measured offset also rides here (AMY bakes volts into the note at the
    edge); in 'track' mode it rides the oscillator const instead."""
    n = CV_BASE_NOTE + CV_PITCH_TRIM_CENTS / 100.0
    if CV_PITCH_MODE == 'gate':
        n += 12.0 * CV_PITCH_SCALE * cv_offset_volts()
    return n


def cv_note_for(raw):
    """The MIDI note a raw pitch reading currently maps to (for the display)."""
    return (CV_BASE_NOTE + CV_PITCH_TRIM_CENTS / 100.0
            + 12.0 * CV_PITCH_SCALE * (raw + cv_offset_volts()))


# --------------------------------------------------------------------------
#  WHY FOUR SYNTHS, NOT ONE SYNTH WITH FOUR VOICES
# --------------------------------------------------------------------------
#  docs/synth.md is explicit: a command addressed to a synth is routed to the
#  matching oscillator IN EVERY ONE OF ITS VOICES.  There is no way to address
#  one voice of a synth differently from another -- that is the whole point of
#  the abstraction.  So a single 4-voice synth CANNOT hold four different
#  detunes, four different pans, or four different wavetable-position offsets:
#  every voice would get the last value sent.  4x UNISON with per-voice detune,
#  which the brief calls the primary mode, is simply not expressible that way.
#
#  Four single-voice synths solve it exactly.  Each carries its own detune,
#  pan, and position offset, and the three voice modes become three ALLOCATION
#  POLICIES over the same fixed set of AMY objects:
#
#      MONO    -> voice 0 only, portamento on, last-note priority
#      UNISON  -> one note to all four voices, each at its own detune/pan
#      POLY    -> notes distributed across the four, oldest-stolen
#
#  Nothing is created or destroyed when the mode changes -- only which voices
#  get sent the note, and a cheap resend of the freq/pan coefficients.  That is
#  the brief's "make voice allocation efficient so switching between modes does
#  not create unnecessary AMY objects", and it also means a mode change never
#  cuts a held note the way a reallocation would.
#
#  It also fixes something the Megatron build documented but could not use:
#  per-osc `pan` is INERT inside a chain, because AMY pans the whole collected
#  chain buffer once, through the HEAD's pan.  With one synth per voice, the
#  head's pan IS the voice's pan -- so stereo spread across a unison stack
#  works, where per-osc pan inside a single chain never could.
# --------------------------------------------------------------------------
VOICE_SYNTHS = [WT_SYNTH0 + i for i in range(NVOICE)]

VOICE_MODES = ["MONO", "UNISON", "POLY"]
VM_MONO, VM_UNISON, VM_POLY = 0, 1, 2

# Unison detune curve, -1..+1 across the four voices.  At DETUNE = 15 cents
# this produces exactly the brief's example spread: -15 / -5 / +5 / +15.
UNI_DETUNE = [-1.0, -1.0 / 3.0, 1.0 / 3.0, 1.0]
# Stereo positions for the unison stack, -1..+1 (scaled by WIDTH).
UNI_PAN = [-1.0, 0.45, -0.45, 1.0]
# Deliberately non-aligned start phases, so a unison stack does not collapse
# into one big oscillator on the attack.
UNI_PHASE = [0.00, 0.37, 0.61, 0.19]
# Per-voice wavetable-position trim, scaled by POS SPR -- the "small per-voice
# variations" the brief asks for, and the cheapest way to stop a unison stack
# sounding like one oscillator turned up loud.
UNI_POS = [-1.0, 0.4, -0.4, 1.0]

LFO_SHAPES = ["SINE", "TRI", "SAW", "RAMP", "SQR", "S&H"]
# S&H is NOISE: AMY's NOISE oscillator is sample-and-hold-ish at the block
# rate when used as a mod source, which is what an S&H LFO is for.
LFO_WAVE = [W_SINE, W_TRIANGLE, W_SAW_DOWN, W_SAW_UP, W_PULSE, W_NOISE]
MOD_RATE_MODES = ["LFO", "AUDIO"]
POLARITY = ["BIPOL", "UNIPOL"]
EG_CURVES = ["RC", "LIN", "DX7", "EXP"]
FILTERS = ["OFF", "LP12", "BP", "HP", "LP24", "NOTCH", "PHASR"]
ONOFF = ["OFF", "ON"]

# Tempo-sync divisions, in beats.  Rate becomes tempo/division when TSYNC is on.
# Index 0 is OFF -- the free-running rate in Hz -- so tempo sync is one enum
# rather than a separate on/off row competing for the eight-row ceiling.
SYNC_DIVS = ["OFF", "4", "2", "1", "1/2", "1/4", "1/8", "1/16"]
SYNC_BEATS = [0.0, 4.0, 2.0, 1.0, 0.5, 0.25, 0.125, 0.0625]


# --------------------------------------------------------------------------
#  MODULATION DESTINATIONS
# --------------------------------------------------------------------------
#  (id, 4-char label, scope, unit)
#
#  scope  'a'/'b'  = the wavetable oscillator, 'h' = the SILENT head
#  unit   'lin'    = the destination's const adds directly (duty, pan)
#         'oct'    = mod terms are OCTAVES on a const in Hz / linear gain
#                    (freq, filter_freq, dist_drive) -- so a polarity offset
#                    has to MULTIPLY the const, not add to it
#         'amp'    = amp coefficients, which combine in the LOG domain rather
#                    than adding; no polarity compensation is possible, so
#                    these routings go through raw (documented, not silent)
#
#  Adding a destination later is one row here plus one branch in coefs_for();
#  the matrix, the UI and the patch format all read this table.
DESTS = [
    ("a_pos", "A.POS", 'a', 'lin'),
    ("b_pos", "B.POS", 'b', 'lin'),
    ("a_pit", "A.PIT", 'a', 'oct'),
    ("b_pit", "B.PIT", 'b', 'oct'),
    ("a_lvl", "A.LVL", 'a', 'amp'),
    ("b_lvl", "B.LVL", 'b', 'amp'),
    ("a_drv", "A.DRV", 'a', 'oct'),
    ("b_drv", "B.DRV", 'b', 'oct'),
    ("cut",   "CUT",   'h', 'oct'),
    ("f_drv", "F.DRV", 'h', 'oct'),
    ("pan",   "PAN",   'h', 'lin'),
]
DEST_IDS = [d[0] for d in DESTS]
DEST_LABELS = [d[1] for d in DESTS]
DEST_SCOPE = dict((d[0], d[2]) for d in DESTS)
DEST_UNIT = dict((d[0], d[3]) for d in DESTS)

# Which coefficient slot each modulator lands in, and which scopes it can
# reach.  MOD1/MOD2 are the two mod-source oscillators, so they are available
# everywhere.  MOD3 is eg1 on the wavetable oscillators and MOD4 is eg1 on the
# head -- an oscillator only has two EGs, and eg0 is already the amp envelope,
# so these two are genuinely scope-limited.  The MATRIX page draws unreachable
# pairs as "--" rather than accepting a value that would do nothing.
MOD_SLOT_COEF = [C_MOD0, C_MOD1, C_EG1, C_EG1]
MOD_SLOT_SCOPES = [('a', 'b', 'h'), ('a', 'b', 'h'), ('a', 'b'), ('h',)]
MOD_IS_ENV = [False, False, True, True]
NMOD = 4


def mod_can_reach(slot, dest_id):
    return DEST_SCOPE[dest_id] in MOD_SLOT_SCOPES[slot]


# --------------------------------------------------------------------------
#  SECTION 2 : PARAMETER MODEL
# --------------------------------------------------------------------------
P = {
    # ---- oscillator A / B ------------------------------------------------
    # "wt" is an INDEX into the wavetable catalogue (see section 3); a patch
    # stores the FILENAME, never the index, so a patch survives the SD card
    # gaining or losing tables.
    # a_pos sits mid-low rather than at 0 so the default MOD1 swing has table
    # on both sides of it -- at 0 the negative half of the LFO is simply
    # clamped away and the movement reads as half-depth.
    "a_wt": 0, "a_pos": 0.35, "a_coarse": 0.0, "a_fine": 0.0,
    "a_lvl": 0.8, "a_phase": 0.0, "a_drv": 1.0, "a_fold": 0,
    # OSC B starts on a DIFFERENT built-in table (SQUARE) and a slight detune,
    # so the two-wavetable architecture is audible the moment you play a note
    # rather than sounding like one oscillator.
    "b_wt": 1, "b_pos": 0.5, "b_coarse": 0.0, "b_fine": 7.0,
    "b_lvl": 0.8, "b_phase": 0.25, "b_drv": 1.0, "b_fold": 0,
    # ---- mix / global ----------------------------------------------------
    "vmode": VM_UNISON, "glide": 0.0, "vsens": 0.4, "phsync": 1,
    "bend": 2.0, "mch": 1, "vol": 4.0, "panic": 0,
    # ---- WT LOAD page: browse + load a user wavetable from SD -------------
    # None of these is a sound parameter -- they drive the SD browser, so a
    # patch never stores them (see PATCH_SKIP).
    "wt_src": 0, "wt_browse": 0, "wt_load": 0, "wt_scan_act": 0,
    # ---- filter ----------------------------------------------------------
    "ftype": 4, "cutoff": 2500.0, "reso": 1.2, "fenv": 1.5,
    "fkbd": 0.35, "fvel": 0.25, "fdrv": 1.0, "fmix": 1.0,
    # ---- amp envelope (eg0 on OSC A and OSC B) ---------------------------
    "aa": 8.0, "ad": 600.0, "as": 0.7, "ar": 350.0, "acurve": 0,
    # ---- MOD 1 / MOD 2 : oscillator modulators ---------------------------
    "m1_shape": 0, "m1_mode": 0, "m1_rate": 0.35, "m1_ratio": 1.0,
    "m1_depth": 1.0, "m1_phase": 0.0, "m1_div": 0,
    "m1_pol": 0, "m1_trig": 1,
    "m2_shape": 1, "m2_mode": 0, "m2_rate": 0.12, "m2_ratio": 2.0,
    "m2_depth": 1.0, "m2_phase": 0.25, "m2_div": 0,
    "m2_pol": 0, "m2_trig": 0,
    # ---- MOD 3 : envelope on the wavetable oscillators (eg1) -------------
    "m3_a": 4.0, "m3_d": 900.0, "m3_s": 0.0, "m3_r": 400.0,
    "m3_curve": 0, "m3_vel": 0.0, "m3_pol": 1,
    # ---- MOD 4 : envelope on the head (eg1).  This IS the filter envelope;
    #      the ENV page's FLT rows and this page edit the same generator.
    "m4_a": 5.0, "m4_d": 700.0, "m4_s": 0.35, "m4_r": 400.0,
    "m4_curve": 0, "m4_vel": 0.25, "m4_pol": 1,
    # ---- matrix editor cursor (not a sound parameter, but it lives in the
    #      grid like one so the encoder can drive it) ----------------------
    "mx_slot": 0, "mx_dest": 0, "mx_amt": 0.0, "mx_clr": 0, "mx_clrall": 0,
    # ---- unison ----------------------------------------------------------
    "uni_det": 15.0, "uni_width": 0.6, "uni_pos": 0.12, "uni_phase": 0.5,
    "uni_drift": 0.2,
    # ---- bus distortion --------------------------------------------------
    "d_drive": 1.0, "d_clip": 0, "d_fold": 0, "d_bits": 24, "d_rate": 1,
    "d_mix": 1.0,
    # ---- chorus / echo ---------------------------------------------------
    "ch_lvl": 0.0, "ch_dly": 320.0, "ch_rate": 0.5, "ch_dep": 0.5,
    "ec_lvl": 0.0, "ec_ms": 300.0, "ec_fb": 0.3, "ec_tone": 0.0,
    # ---- reverb / eq -----------------------------------------------------
    "rv_lvl": 0.12, "rv_live": 0.85, "rv_damp": 0.5, "rv_xover": 3000.0,
    "eq_l": 0.0, "eq_m": 0.0, "eq_h": 0.0,
    # ---- tempo (for MOD tempo sync) --------------------------------------
    "tempo": 120.0,
    # ---- CV CAL page (mirror the CV_* module constants) ------------------
    # These describe THIS rig's CV, not a sound, so they are never stored in a
    # patch (see PATCH_SKIP) -- they live in their own calibration file.
    "cvoff": 0.0, "cvatt": 0.0, "cvgate": 2.5, "cvnote": 60,
}

# The modulation matrix: {(slot, dest_id): amount}.  Sparse on purpose -- only
# routings that exist cost anything, and coefs_for() walks a handful of entries
# rather than a 4x11 array on every parameter change.
MATRIX = {}

# Sensible starting patch: the wavetables move on their own, and MOD4 opens the
# filter, so the synth makes a recognisably "wavetable" noise out of the box
# rather than a static tone.
MATRIX[(0, "a_pos")] = 0.35     # MOD1 (LFO) -> OSC A position
MATRIX[(0, "b_pos")] = -0.25    # ...and OSC B the other way
MATRIX[(2, "a_pos")] = 0.4      # MOD3 (env) -> OSC A position sweep
# MOD4 -> CUTOFF is not stored here: it IS the filter envelope amount, so it
# lives in P["fenv"] and is reached through mx_get/mx_set below.  One store,
# two places to edit it (the FILTER page's ENV AMT row and the MATRIX page).


def mx_get(slot, dest_id):
    if slot == 3 and dest_id == "cut":
        return P["fenv"]
    return MATRIX.get((slot, dest_id), 0.0)


def mx_set(slot, dest_id, amt):
    if slot == 3 and dest_id == "cut":
        P["fenv"] = amt
        return
    if amt == 0.0:
        MATRIX.pop((slot, dest_id), None)
    else:
        MATRIX[(slot, dest_id)] = amt


def mx_routings(scope):
    """Every live routing reaching `scope`, as (slot, dest_id, amount).

    Walks the destination table rather than the MATRIX dict so the synthetic
    MOD4->CUTOFF entry above is included exactly once."""
    out = []
    for dest_id, label, dscope, unit in DESTS:
        if dscope != scope:
            continue
        for slot in range(NMOD):
            if not mod_can_reach(slot, dest_id):
                continue
            amt = mx_get(slot, dest_id)
            if amt != 0.0:
                out.append((slot, dest_id, amt))
    return out


# --------------------------------------------------------------------------
#  SECTION 3 : WAVETABLE MANAGEMENT
# --------------------------------------------------------------------------
#  HOW THIS ACTUALLY WORKS IN AMY -- verified, not assumed:
#
#    oscillators.c render_wavetable() looks its table up with
#    pcm_get_sample_ram_for_preset(synth[osc]->preset), and pcm.c's
#    get_preset_for_preset_number() searches the MEMORY preset list FIRST,
#    falling back to the baked-in ROM presets only if nothing matches.  A
#    memory preset therefore SHADOWS a ROM one.
#
#    So: amy.load_sample("/sd/wavetables/user/foo.wav", preset=N) followed by
#    _amy_send(osc=..., wave=WAVETABLE, preset=N) plays an SD-card wavetable.
#    That is the entire mechanism, and it needs no firmware change.
#
#  TWO CONSTRAINTS THAT FALL OUT OF THE SAME CODE, AND ARE OBEYED HERE:
#
#    1. It must be a RAM sample, not a streamed one.  amy.disk_sample() sets
#       file_handle and leaves sample_ram NULL; render_wavetable() bails out on
#       a NULL table and renders silence.  So wavetables go through
#       load_sample() (RAM) and are never streamed from disk.
#
#    2. RAM is the real budget.  A full 64-cycle table is 16384 samples =
#       32 KB.  Hence WT_SLOTS below: a small LRU of preset slots, so a patch
#       loads the two tables it names and nothing else -- the brief's "avoid
#       loading unnecessary tables into RAM", made concrete.
#
#  Loading is also SLOW: load_sample() pushes the sample over the wire protocol
#  in 94-frame chunks, so a 16384-frame table is ~175 messages.  That is fine
#  on a patch change and disastrous inside loop(), so it only ever happens from
#  an explicit table selection or patch load, with the voices silenced first.
# --------------------------------------------------------------------------
WT_CYCLE = 256                  # WAVETABLE_SAMPLES_PER_CYCLE (oscillators.c)
WT_MIN_SAMPLES = 2 * WT_CYCLE   # render_wavetable needs two cycles to crossfade
WT_FULL = 64 * WT_CYCLE         # the canonical 64-cycle / 16384-sample table

# Preset numbers we load user tables into.  Chosen above AMY's own ranges: ROM
# PCM is 0..18, the Gamma9001 drum banks are 256..391, and 384..390 are the GM
# kit patches.  400+ collides with nothing, and memory presets shadow anyway.
WT_PRESET0 = 400
WT_SLOTS = 4                    # 4 x 32 KB worst case; a patch only needs 2

# ---- built-in wavetables -------------------------------------------------
# The firmware ROM wavetables (GAMMA9001 preset 19..23) barely morph and sound
# nearly identical -- measured directly against AMY's renderer -- so the synth
# ships its OWN wavetables instead, computed in Python at boot/on demand and
# loaded into RAM.  Each one sweeps a wide timbral range as POSITION moves
# across its cycles (validated: SAW goes 4 -> 72 significant harmonics, vs the
# ROM tables' ~2).  No SD card and no firmware change needed.  The ROM base is
# kept only as a last-ditch fallback if a generate ever fails.
WT_BUILTIN_BASE = 19            # ROM fallback preset (GAMMA9001)
WT_GEN_BASE = 360              # procedural built-ins live at 360..; below the
                               # SD LRU range (WT_PRESET0=400) so they never
                               # collide or get evicted.
WT_GEN_CYCLES = 16            # cycles per generated table (16*256 = 4096 smp)
_wt_gen_loaded = set()        # built-in indices already generated into RAM


def _wt_norm_cycle(cyc):
    """Scale one cycle to just under full scale -- per-cycle, so POSITION reads
    as a timbre change rather than a volume ramp."""
    pk = 1e-9
    for x in cyc:
        a = x if x >= 0 else -x
        if a > pk:
            pk = a
    g = 0.95 / pk
    return [x * g for x in cyc]


def _wt_gen_saw(ph, m):
    """Sine at POSITION 0, bright saw at 1 (harmonics fill in)."""
    return math.sin(6.2831853 * ph) * (1.0 - m) + (2.0 * ph - 1.0) * m


def _wt_gen_square(ph, m):
    """Pulse width sweeping from a thin spike to a full square."""
    return 1.0 if ph < (0.5 - 0.45 * (1.0 - m)) else -1.0


def _wt_gen_harm(ph, m):
    """Additive: one more harmonic joins per cycle -- an organ-like build."""
    n = 1 + int(m * 15)
    v = 0.0
    h = 1
    while h <= n:
        v += math.sin(6.2831853 * h * ph) / h
        h += 1
    return v


def _wt_gen_vox(ph, m):
    """A vocal-ish pair of formants sliding up the table."""
    f1 = 1.0 + m * 5.0
    f2 = 4.0 + m * 14.0
    return (math.sin(6.2831853 * ph) * 0.6
            + math.sin(6.2831853 * f1 * ph) * 0.3
            + math.sin(6.2831853 * f2 * ph) * 0.25 * m)


def _wt_gen_fold(ph, m):
    """A sine driven progressively into a triangle wavefolder."""
    v = math.sin(6.2831853 * ph) * (1.0 + m * 5.0)
    g = 0
    while g < 4:
        if v > 1.0:
            v = 2.0 - v
        elif v < -1.0:
            v = -2.0 - v
        g += 1
    return v


def _wt_gen_bell(ph, m):
    """Inharmonic partials fading in -- metallic, very responsive to FM."""
    r = (1.0, 2.41, 3.83, 5.17, 7.61)
    v = 0.0
    i = 0
    while i < len(r):
        v += math.sin(6.2831853 * r[i] * ph) * (1.0 / (i + 1)) * (m if i else 1.0)
        i += 1
    return v


# Name + generator.  The first two (cheap: 1 and 0 sin() per sample) are the
# boot defaults, so start-up only generates those; the richer tables generate
# lazily the first time they are selected.
WT_BUILTIN = (
    ("SAW", _wt_gen_saw),
    ("SQUARE", _wt_gen_square),
    ("HARM", _wt_gen_harm),
    ("VOX", _wt_gen_vox),
    ("FOLD", _wt_gen_fold),
    ("BELL", _wt_gen_bell),
)
WT_BUILTIN_COUNT = len(WT_BUILTIN)


def _wt_build_gen(fn):
    """Render a generator into 16-bit mono LE bytes (WT_GEN_CYCLES * 256)."""
    out = bytearray(WT_GEN_CYCLES * WT_CYCLE * 2)
    oi = 0
    denom = float(WT_GEN_CYCLES - 1)
    for c in range(WT_GEN_CYCLES):
        m = c / denom
        cyc = [fn(i / float(WT_CYCLE), m) for i in range(WT_CYCLE)]
        cyc = _wt_norm_cycle(cyc)
        for x in cyc:
            s = int(x * 32767.0)
            if s > 32767:
                s = 32767
            elif s < -32768:
                s = -32768
            out[oi] = s & 0xFF
            out[oi + 1] = (s >> 8) & 0xFF
            oi += 2
    return bytes(out)

# The SD card is scanned RECURSIVELY from its mount root, wherever the user
# put their files -- not a fixed /wavetables/{factory,user} layout, which was
# the reason the browser showed nothing.  Bounded so a huge card cannot hang
# the scan.  Dot-files and the usual OS metadata folders are skipped.
SD_SCAN_MAX_DEPTH = 5
SD_SCAN_MAX_FILES = 250
_SD_SKIP = ("System Volume Information", ".Spotlight-V100", ".Trashes",
            ".fseventsd", "__MACOSX", ".git")

# STARTUP CONTRACT: the synth ALWAYS boots on the built-in tables (INT 0..4)
# and never reads the SD card on its own -- a missing, slow or unformatted card
# can never stall or break startup.  SD tables are pulled in only deliberately,
# from the WT LOAD page, or automatically when a saved patch names one.  PR
# shorepine/amy#997 widened what counts as a wavetable: ANY PCM .wav of at
# least two 256-sample cycles (>= 512 samples) works now, not just
# purpose-built 64-cycle tables, so the browser offers every .wav on the card
# and an unusable one is caught at load time rather than being pre-filtered.


def _sd_card_root():
    """The SD card mount point.

    Uses the same path AMYboard's own SD sketches use -- tulip.root_dir()
    + 'sd' -- then falls back to a couple of common mounts.  Returns None if no
    readable mount is found, so the caller can say 'no card' rather than
    scanning nonsense."""
    cands = []
    try:
        r = tulip.root_dir()
        if not r.endswith("/"):
            r += "/"
        cands.append(r + "sd")
    except Exception:
        pass
    cands += ["/sd", "/flash", "/user"]
    for p in cands:
        try:
            os.listdir(p)
            return p
        except Exception:
            continue
    return None


def _sd_iter(dirpath):
    """Yield (name, is_dir) for one directory.

    Prefers os.ilistdir (whose entry[1] type field flags a directory as
    0x4000, exactly as AMYboard's file-browser sketch relies on); falls back to
    os.listdir + os.stat where ilistdir is absent.  Never raises."""
    try:
        for entry in os.ilistdir(dirpath):
            name = entry[0]
            etype = entry[1] if len(entry) > 1 else None
            yield name, (etype == 0x4000)
        return
    except AttributeError:
        pass
    except OSError:
        return
    try:
        names = os.listdir(dirpath)
    except OSError:
        return
    for name in names:
        is_dir = False
        try:
            is_dir = (os.stat(dirpath + "/" + name)[0] & 0x4000) != 0
        except Exception:
            pass
        yield name, is_dir


WT_ROOT = None          # resolved by the first SD scan

# The catalogue the OSC A/B TABLE knobs scroll through: a list of
# (display_name, path_or_None, builtin_preset_or_None).  It holds the built-in
# tables ALWAYS, plus any SD tables that have been explicitly loaded (WT LOAD
# page) or pulled in by a patch.  Built-ins come first, so index 0 is always
# valid.  It is NOT populated from the card at boot.
WT_CATALOG = []

# Files discovered on the SD card by an explicit scan, as (display, path).
# This is the BROWSE list for the WT LOAD page, kept separate from the
# catalogue: scanning shows you what is on the card; loading is what commits a
# file to a preset slot and RAM and adds it to the catalogue.
_sd_files = []

# path -> preset slot, plus an LRU of slot usage.
_wt_slot_of = {}
_wt_slot_lru = []
_wt_failed = set()      # paths that would not load; never retried automatically


def _file_exists(path):
    try:
        os.stat(path)
        return True
    except Exception:
        return False


def wt_builtins():
    """Reset the catalogue to the built-in (procedural) tables alone.

    Called at boot.  Entries carry their generator in the third slot (a
    callable); wt_preset_for() renders it into RAM on first use.  No SD access
    and no firmware wavetables involved, honouring the STARTUP CONTRACT above."""
    global WT_CATALOG
    WT_CATALOG = [(name, None, fn) for (name, fn) in WT_BUILTIN]
    return len(WT_CATALOG)


def _wt_gen_preset(idx, fn):
    """RAM preset for procedural built-in `idx`, generating it on first use.

    Returns the preset number, or None if generation/loading fails (caller
    then falls back to a firmware ROM table)."""
    preset = WT_GEN_BASE + idx
    if idx in _wt_gen_loaded:
        return preset
    try:
        data = _wt_build_gen(fn)
    except Exception as e:
        print("wt: generate failed for built-in %d -- %s" % (idx, e))
        return None
    try:
        lsb = getattr(amy, "load_sample_bytes", None)
        if lsb is not None:
            lsb(data, preset=preset, midinote=60, sr=SR)
        else:
            amy.send(load_sample="%d,%d,%d,60,0,0"
                     % (preset, len(data) // 2, SR))
            b64 = getattr(amy, "b64", None)
            chunk = getattr(amy, "_send_transfer_chunk", None) or amy.send_raw
            if b64 is None:
                import binascii
                b64 = lambda b: binascii.b2a_base64(b)[:-1]
            for i in range(0, len(data), 188):
                chunk(b64(data[i:i + 188]).decode('ascii'))
    except Exception as e:
        print("wt: load of built-in %d failed -- %s" % (idx, e))
        return None
    _wt_gen_loaded.add(idx)
    return preset


def wt_scan_sd():
    """Recursively find every .wav/.wt on the SD card, WITHOUT loading any.

    Walks the whole card from its mount root, so a file is found wherever the
    user dropped it -- the old fixed /wavetables/{factory,user} scan was why
    'nothing shows up'.  Populates the BROWSE list for the WT LOAD page as
    (display, fullpath), display being the path relative to the card root so
    two same-named files in different folders stay tellable apart.  Bounded by
    depth and count, and never raises: a missing card just yields an empty
    list.  Every .wav/.wt is offered (PR#997); an unusable one is rejected at
    load, not hidden here."""
    global WT_ROOT, _sd_files
    _sd_files = []
    root = _sd_card_root()
    WT_ROOT = root
    if root is None:
        return 0
    # Depth-first walk with an explicit stack (no recursion depth worries on
    # MicroPython).  Directories are pushed to be visited; files are collected.
    stack = [(root, 0)]
    while stack and len(_sd_files) < SD_SCAN_MAX_FILES:
        dirpath, depth = stack.pop()
        subdirs = []
        for name, is_dir in _sd_iter(dirpath):
            if name in _SD_SKIP or name.startswith("."):
                continue
            full = dirpath + "/" + name
            if is_dir:
                if depth < SD_SCAN_MAX_DEPTH:
                    subdirs.append((full, depth + 1))
            else:
                ln = name.lower()
                if ln.endswith(".wav") or ln.endswith(".wt"):
                    rel = full[len(root) + 1:]
                    _sd_files.append((rel, full))
        stack.extend(reversed(subdirs))
    _sd_files.sort(key=lambda e: e[0].lower())
    return len(_sd_files)


def wt_add_path(path, disp=None):
    """Add an SD table to the catalogue if not already present; return its
    catalogue index.  How a browsed file -- or a patch's stored filename --
    becomes selectable on the TABLE knob."""
    i = wt_index_of_path(path)
    if i >= 0:
        return i
    if disp is None:
        disp = path.rsplit("/", 1)[-1].rsplit(".", 1)[0]
    WT_CATALOG.append((disp[:12], path, None))
    return len(WT_CATALOG) - 1


def wt_count():
    return len(WT_CATALOG) if WT_CATALOG else 1


def wt_name(idx):
    if not WT_CATALOG:
        return "-"
    return WT_CATALOG[int(clamp(idx, 0, len(WT_CATALOG) - 1))][0]


def wt_path(idx):
    if not WT_CATALOG:
        return None
    return WT_CATALOG[int(clamp(idx, 0, len(WT_CATALOG) - 1))][1]


def _wt_table_id(idx):
    """A stable id for catalogue entry `idx` -- ("gen", idx) for a built-in, the
    path for an SD table, ("rom", n) for a ROM fallback.  Used to key the
    preview cache."""
    idx = int(clamp(idx, 0, len(WT_CATALOG) - 1))
    name, path, builtin = WT_CATALOG[idx]
    return ("gen", idx) if callable(builtin) else (path if path else ("rom", builtin))


def _wt_preview_for(idx):
    """The downsampled cycle preview for catalogue entry `idx`, or None.

    Built on demand from the generator (built-in) or from the samples captured
    at load (SD), then cached by table id so the display costs nothing per
    frame."""
    if not WT_CATALOG:
        return None
    idx = int(clamp(idx, 0, len(WT_CATALOG) - 1))
    name, path, builtin = WT_CATALOG[idx]
    tid = _wt_table_id(idx)
    pv = _wt_prev_cache.get(tid)
    if pv is not None:
        return pv
    if callable(builtin):
        pv = _preview_from_gen(builtin)
    elif path is not None:
        pv = _wt_sample_preview.get(path)
    else:
        pv = None                       # ROM fallback: no sample data in Python
    if pv is not None:
        _wt_prev_cache[tid] = pv
    return pv


def _sd_basename(rel):
    """Filename (no folders, no extension) from a browse-list relative path."""
    return rel.rsplit("/", 1)[-1].rsplit(".", 1)[0]


def _sd_name(idx):
    """Display name for a BROWSE-list entry (WT LOAD 'FILE' row).

    Shows the bare filename -- the folder path is only there to disambiguate,
    and the focus row / browser pane show more of it."""
    if not _sd_files:
        return "--SCAN--"
    return _sd_basename(_sd_files[int(clamp(idx, 0, len(_sd_files) - 1))][0])


def wt_index_of_path(path):
    """Catalogue index for a stored patch filename, or -1 if it is gone.

    Patches store the PATH, so a table that moved or was deleted is detected
    here and reported, rather than silently selecting whatever now sits at the
    old index."""
    for i in range(len(WT_CATALOG)):
        if WT_CATALOG[i][1] == path:
            return i
    return -1


# --------------------------------------------------------------------------
#  WAV DECODING  --  read ANY common WAV, not just 16-bit integer PCM
# --------------------------------------------------------------------------
#  This is the fix for "unable to load".  amy.load_sample() parses the file
#  through amy.wave, whose _read_fmt_chunk RAISES on anything but
#  WAVE_FORMAT_PCM (0x0001) -- so a 32-bit float or WAVE_FORMAT_EXTENSIBLE
#  file (what Serum, Vital, WaveEdit and most DAWs export) fails outright.
#
#  So we decode the WAV ourselves: 8/16/24/32-bit integer PCM, 32-bit IEEE
#  float, and EXTENSIBLE (whose real format is its SubFormat GUID) are all
#  accepted, stereo is downmixed to mono, and the result is handed to AMY as
#  plain 16-bit mono frames via load_sample_bytes -- the format wave=WAVETABLE
#  wants.  Anything genuinely unusable raises a ValueError with a short reason
#  the UI can show.
WT_LOAD_MAX_FRAMES = 1 << 16    # cap so a multi-MB sample can't OOM the load
_wt_last_error = ""             # reason string from the most recent failed load

_WAV_FMT_PCM = 0x0001
_WAV_FMT_FLOAT = 0x0003
_WAV_FMT_EXTENSIBLE = 0xFFFE


def _wav_read_header(f):
    """Parse RIFF/WAVE header. Returns (fmt_tag, nch, sr, bits, data_pos,
    data_size).  Raises ValueError with a short reason on anything malformed."""
    riff = f.read(12)
    if len(riff) < 12 or riff[0:4] != b'RIFF' or riff[8:12] != b'WAVE':
        raise ValueError("not a WAV")
    fmt_tag = None
    nch = 1
    sr = 44100
    bits = 16
    while True:
        hdr = f.read(8)
        if len(hdr) < 8:
            break
        cid = hdr[0:4]
        csize = struct.unpack('<I', hdr[4:8])[0]
        if cid == b'fmt ':
            fmt = f.read(csize)
            if len(fmt) < 16:
                raise ValueError("bad fmt chunk")
            fmt_tag, nch, sr, _br, _al, bits = struct.unpack('<HHIIHH', fmt[:16])
            if fmt_tag == _WAV_FMT_EXTENSIBLE and len(fmt) >= 26:
                # The real format lives in the first 2 bytes of the SubFormat GUID.
                fmt_tag = struct.unpack('<H', fmt[24:26])[0]
            if csize & 1:
                f.read(1)
        elif cid == b'data':
            return fmt_tag, nch, sr, bits, f.tell(), csize
        else:
            # Skip any other chunk (LIST/INFO/cue/smpl/...), honouring padding.
            f.seek(csize + (csize & 1), 1)
    raise ValueError("no data chunk")


def _wav_to_mono16(path):
    """Decode `path` to (mono 16-bit LE bytes, samplerate, nframes).

    Trims to a whole number of 256-sample cycles so the wavetable crossfade
    lands cleanly, and caps overly long files.  Raises ValueError on an
    unreadable or unsupported file."""
    f = open(path, 'rb')
    try:
        fmt_tag, nch, sr, bits, data_pos, data_size = _wav_read_header(f)
        if fmt_tag is None:
            raise ValueError("no fmt chunk")
        bytes_per = (bits + 7) // 8
        frame_bytes = nch * bytes_per
        if frame_bytes == 0:
            raise ValueError("bad WAV header")
        nframes = data_size // frame_bytes
        if nframes > WT_LOAD_MAX_FRAMES:
            nframes = WT_LOAD_MAX_FRAMES
        nframes = (nframes // WT_CYCLE) * WT_CYCLE     # whole cycles only
        if nframes < WT_MIN_SAMPLES:
            raise ValueError("too short (<512 smp)")

        is_float = (fmt_tag == _WAV_FMT_FLOAT)
        is_pcm = (fmt_tag == _WAV_FMT_PCM)
        if not (is_pcm or is_float):
            raise ValueError("fmt 0x%X unsupported" % fmt_tag)
        if is_float and bytes_per != 4:
            raise ValueError("float%d unsupported" % bits)

        f.seek(data_pos)
        # Fast path: already 16-bit mono PCM -- copy the bytes straight through.
        if is_pcm and bits == 16 and nch == 1:
            return f.read(nframes * 2), sr, nframes

        out = bytearray(nframes * 2)
        oi = 0
        remaining = nframes
        BLK = 1024
        while remaining > 0:
            n = BLK if remaining > BLK else remaining
            raw = f.read(n * frame_bytes)
            got = len(raw) // frame_bytes
            if got == 0:
                break
            if got < n:
                n = got
            for fr in range(n):
                base = fr * frame_bytes
                acc = 0
                for ch in range(nch):
                    o = base + ch * bytes_per
                    if is_float:
                        v = struct.unpack_from('<f', raw, o)[0]
                        s = int(max(-1.0, min(1.0, v)) * 32767.0)
                    elif bytes_per == 2:
                        s = struct.unpack_from('<h', raw, o)[0]
                    elif bytes_per == 1:
                        s = (raw[o] - 128) << 8          # 8-bit WAV is unsigned
                    elif bytes_per == 3:
                        val = raw[o] | (raw[o + 1] << 8) | (raw[o + 2] << 16)
                        if val & 0x800000:
                            val -= 1 << 24
                        s = val >> 8
                    elif bytes_per == 4:
                        s = struct.unpack_from('<i', raw, o)[0] >> 16
                    else:
                        raise ValueError("bit depth %d" % bits)
                    acc += s
                s = acc // nch
                if s > 32767:
                    s = 32767
                elif s < -32768:
                    s = -32768
                out[oi] = s & 0xFF
                out[oi + 1] = (s >> 8) & 0xFF
                oi += 2
            remaining -= n
        return bytes(out[:oi]), sr, oi // 2
    finally:
        f.close()


# --------------------------------------------------------------------------
#  WAVETABLE PREVIEW  --  data for the topographic (waterfall) display
# --------------------------------------------------------------------------
#  A tiny downsampled copy of each table's cycles: WT_PREV_LINES frames, each
#  WT_PREV_PTS points in -1..1.  Cheap to hold (a few hundred floats per table)
#  and to draw.  Built from the generator for a built-in, and from the decoded
#  samples for an SD table (captured once at load).  Keyed by table id so the
#  OSC A/B pane can look it up without recomputing on every redraw.
WT_PREV_LINES = 16
WT_PREV_PTS = 44
_wt_prev_cache = {}          # table-id -> list[WT_PREV_LINES] of list[WT_PREV_PTS]
_wt_sample_preview = {}      # SD path -> preview (captured at load time)


def _norm_row(row):
    pk = 1e-9
    for v in row:
        a = v if v >= 0 else -v
        if a > pk:
            pk = a
    g = 1.0 / pk
    return [v * g for v in row]


def _preview_from_gen(fn):
    lines = []
    for c in range(WT_PREV_LINES):
        m = c / float(WT_PREV_LINES - 1)
        row = [fn(i / float(WT_PREV_PTS), m) for i in range(WT_PREV_PTS)]
        lines.append(_norm_row(row))
    return lines


def _preview_from_samples(mono):
    """Downsample decoded 16-bit LE mono bytes into the preview grid."""
    total = len(mono) // 2
    ncyc = total // WT_CYCLE
    if ncyc < 2:
        return None
    lines = []
    for li in range(WT_PREV_LINES):
        c = int(li * (ncyc - 1) / float(WT_PREV_LINES - 1))
        base = c * WT_CYCLE
        row = []
        for i in range(WT_PREV_PTS):
            si = base + int(i * (WT_CYCLE - 1) / float(WT_PREV_PTS - 1))
            row.append(struct.unpack_from('<h', mono, si * 2)[0] / 32768.0)
        lines.append(_norm_row(row))
    return lines


def _wt_stream_file(path, slot):
    """Decode `path` and stream it into AMY preset `slot` as a wavetable.

    Returns the frame count on success.  Raises ValueError (with a short
    reason) on any failure -- caller blacklists and reports it."""
    mono, sr, nframes = _wav_to_mono16(path)
    if nframes < WT_MIN_SAMPLES:
        raise ValueError("too short (<512 smp)")
    # Capture a preview for the topographic display.
    try:
        pv = _preview_from_samples(mono)
        if pv is not None:
            _wt_sample_preview[path] = pv
    except Exception:
        pass
    # load_sample_bytes is the public path that handles the wire/transfer
    # chunking; fall back to the raw header+chunk protocol if a stripped build
    # doesn't expose it.
    lsb = getattr(amy, "load_sample_bytes", None)
    if lsb is not None:
        lsb(mono, preset=slot, midinote=60, sr=sr)
    else:
        amy.send(load_sample="%d,%d,%d,60,0,0" % (slot, nframes, sr))
        b64 = getattr(amy, "b64", None)
        chunk = getattr(amy, "_send_transfer_chunk", None) or amy.send_raw
        if b64 is None:
            import binascii
            b64 = lambda b: binascii.b2a_base64(b)[:-1]
        step = 188
        for i in range(0, len(mono), step):
            chunk(b64(mono[i:i + step]).decode('ascii'))
    return nframes


def _wt_claim_slot(path):
    """Reserve a preset slot for `path`, evicting the least-recently-used.

    Returns (preset_number, already_loaded)."""
    if path in _wt_slot_of:
        slot = _wt_slot_of[path]
        if path in _wt_slot_lru:
            _wt_slot_lru.remove(path)
        _wt_slot_lru.append(path)
        return slot, True
    used = set(_wt_slot_of.values())
    slot = None
    for s in range(WT_PRESET0, WT_PRESET0 + WT_SLOTS):
        if s not in used:
            slot = s
            break
    if slot is None:
        # Evict the oldest table.  amy.unload_sample() frees its RAM -- without
        # this the memory preset list would just keep growing.
        victim = _wt_slot_lru.pop(0)
        slot = _wt_slot_of.pop(victim)
        try:
            amy.unload_sample(slot)
        except Exception as e:
            print("wt: unload of preset", slot, "failed:", e)
    _wt_slot_of[path] = slot
    _wt_slot_lru.append(path)
    return slot, False


def wt_preset_for(idx):
    """The AMY preset number to play for catalogue entry `idx`, loading the
    table into RAM if it is not already there.

    Returns None if the entry cannot be played, in which case the caller falls
    back to a built-in.  Every failure path is handled: missing file, unreadable
    WAV, a table too short for AMY to crossfade, and a load that throws."""
    if not WT_CATALOG:
        return WT_BUILTIN_BASE
    idx = int(clamp(idx, 0, len(WT_CATALOG) - 1))
    name, path, builtin = WT_CATALOG[idx]
    if callable(builtin):
        # Procedural built-in: render + load on first use, ROM as last resort.
        pr = _wt_gen_preset(idx, builtin)
        return pr if pr is not None else WT_BUILTIN_BASE
    if builtin is not None:
        return builtin              # a firmware ROM preset (fallback only)
    if path in _wt_failed:
        return None
    if not _file_exists(path):
        _wt_note_fail(path, "missing file")
        return None
    slot, loaded = _wt_claim_slot(path)
    if loaded:
        return slot
    try:
        n = _wt_stream_file(path, slot)
        print("wt: loaded %s -- %d frames into preset %d" % (path, n, slot))
    except Exception as e:
        # The slot was reserved but nothing usable landed in it; release it so
        # a later good table can reuse it, and remember why this one failed.
        _wt_slot_of.pop(path, None)
        if path in _wt_slot_lru:
            _wt_slot_lru.remove(path)
        _wt_note_fail(path, str(e))
        return None
    return slot


def _wt_note_fail(path, reason):
    global _wt_last_error
    _wt_last_error = reason
    _wt_failed.add(path)
    print("wt: cannot load %s -- %s" % (path, reason))


def wt_preset_or_fallback(idx):
    p = wt_preset_for(idx)
    if p is None:
        toast("WT LOAD FAIL")
        return WT_BUILTIN_BASE
    return p


_a_wt_path = None       # path the patch asked for, or None for a built-in
_b_wt_path = None


def wt_rescan():
    """Re-read the card (an SD swap, or tables copied over while running).

    Refreshes the BROWSE list and clears the failure blacklist so a table that
    went missing gets another chance.  Also re-resolves the two patch table
    paths: if a card swap brought a referenced table back, it rejoins the
    catalogue and the oscillator points at it again.  Does not disturb what is
    already loaded in RAM."""
    _wt_failed.clear()
    _wt_prev_cache.clear()          # a card swap may replace a same-named file
    _wt_sample_preview.clear()
    n = wt_scan_sd()
    for path, key in ((_a_wt_path, "a_wt"), (_b_wt_path, "b_wt")):
        if path is not None and wt_index_of_path(path) < 0 and _file_exists(path):
            P[key] = wt_add_path(path)
    return n


def wt_remember_selection():
    """Record the current selections as PATHS, for the patch file."""
    global _a_wt_path, _b_wt_path
    _a_wt_path = wt_path(P["a_wt"])
    _b_wt_path = wt_path(P["b_wt"])


# --------------------------------------------------------------------------
#  SECTION 4 : OSCILLATOR CONFIGURATION AND THE MODULATION MATRIX
# --------------------------------------------------------------------------
#  Everything below builds AMY ControlCoefficient strings.  This is the whole
#  point of the design: the matrix is evaluated HERE, in Python, once per
#  parameter change or note -- never per sample and never per loop() tick --
#  and the result is a set of coefficients that AMY's DSP then applies at audio
#  rate for free.  There is no per-sample arithmetic anywhere in this file.
#
#  A coefficient list is 10 slots (see C_* above).  A slot left None is sent as
#  an empty field, which AMY reads as "leave this one alone" -- so we only ever
#  transmit what we actually mean to set.
# --------------------------------------------------------------------------

def coef_str(c):
    """Render a coefficient list, trimming trailing unspecified slots."""
    n = len(c)
    while n > 0 and c[n - 1] is None:
        n -= 1
    out = []
    for i in range(n):
        v = c[i]
        out.append("" if v is None else ("%.4f" % v).rstrip("0").rstrip("."))
    return ",".join(out)


def mod_terms(slot, amt, unit):
    """(const_offset, coefficient) for one routing, honouring its polarity.

    AMY has no bipolar envelope and no unipolar oscillator: an EG runs 0..1 and
    an oscillator swings +/-1.  Both polarities are still delivered exactly, by
    moving the destination's CONST term to compensate --

        LFO, bipolar   : swings -amt..+amt about const   (natural)
        LFO, unipolar  : coef amt/2, const +amt/2  -> const..const+amt
        ENV, unipolar  : rises 0..amt from const          (natural)
        ENV, bipolar   : coef 2*amt, const -amt    -> const-amt..const+amt

    `unit` decides how the offset is applied by the caller: 'lin' adds it,
    'oct' multiplies the const by 2**offset (freq / filter_freq / dist_drive
    coefficients are octaves on a const in Hz or linear gain), and 'amp' takes
    no offset at all -- amp coefficients combine in the LOG domain rather than
    summing, so there is no const term that would shift a log-combined
    modulation by a fixed amount.  That last case is a documented limit, not an
    oversight; an amp routing is simply always its natural polarity."""
    if unit == 'amp':
        return 0.0, amt
    unipolar = P["m%d_pol" % (slot + 1)] == 1
    if MOD_IS_ENV[slot]:
        if unipolar:
            return 0.0, amt
        return -amt, 2.0 * amt
    if unipolar:
        return amt * 0.5, amt * 0.5
    return 0.0, amt


def _apply_routings(coefs, dest_id, const, unit):
    """Fold every live routing to `dest_id` into `coefs`, returning the new
    const.  One place, so adding a destination never means remembering to
    update the polarity or scope logic again."""
    for slot in range(NMOD):
        if not mod_can_reach(slot, dest_id):
            continue
        amt = mx_get(slot, dest_id)
        if amt == 0.0:
            continue
        off, coef = mod_terms(slot, amt, unit)
        idx = MOD_SLOT_COEF[slot]
        coefs[idx] = (coefs[idx] or 0.0) + coef
        if unit == 'lin':
            const += off
        elif unit == 'oct' and off != 0.0:
            const *= 2.0 ** off
    return const


def _up_octaves(dest_id, extra=0.0):
    """Worst-case UPWARD modulation on a destination, in octaves.

    Used to keep a resonant filter under FILT_CEILING: AMY does not clamp the
    summed filter_freq coefficients, and a biquad driven past Nyquist goes
    unstable and rings at a fixed pitch on every note."""
    up = extra
    for slot in range(NMOD):
        if not mod_can_reach(slot, dest_id):
            continue
        amt = mx_get(slot, dest_id)
        if amt <= 0.0:
            continue
        off, coef = mod_terms(slot, amt, 'oct')
        up += abs(coef) + max(0.0, off)
    return up


# ---- per-voice offsets ----------------------------------------------------
#  These are what make four separate synths worth having.  In MONO and POLY
#  every voice is an independent note, so they all sit at zero; in UNISON they
#  spread the stack.

def _unison_active():
    return int(P["vmode"]) == VM_UNISON


def voice_cents(v):
    if not _unison_active():
        return 0.0
    return UNI_DETUNE[v] * P["uni_det"] + _drift_cents[v]


def voice_pan(v):
    if not _unison_active():
        return 0.5
    return clamp(0.5 + UNI_PAN[v] * P["uni_width"] * 0.5, 0.0, 1.0)


def voice_pos_offset(v):
    if not _unison_active():
        return 0.0
    return UNI_POS[v] * P["uni_pos"]


def voice_phase(v, base):
    if not _unison_active():
        return base
    return (base + UNI_PHASE[v] * P["uni_phase"]) % 1.0


# ---- coefficient builders -------------------------------------------------

def osc_freq_coefs(which, v):
    """freq for OSC A or B of voice v.

    The pitch offset is a freq COEFFICIENT CONST in Hz, never a per-osc note --
    a chained oscillator refuses notes outright (role SYNTH_IS_CHAINED), which
    is the single most expensive lesson from the Megatron build.  A const of
    REF_HZ * 2**(semitones/12) is a pure log-domain offset riding on whatever
    note the head is playing.

    `bend` MUST stay 1.0: AMY's default freq coefs are 0,1,0,0,0,0,1 and pitch
    bend rides that last slot, so sending freq at all means re-asserting it or
    the bend wheel goes dead."""
    semis = P[which + "_coarse"] + P[which + "_fine"] / 100.0 + voice_cents(v) / 100.0
    const = REF_HZ * (2.0 ** (semis / 12.0))
    c = [None] * NCOEF
    c[C_NOTE] = 1.0
    c[C_BEND] = 1.0
    const = _apply_routings(c, which + "_pit", const, 'oct')
    # CV IN (track mode): the 1V/oct pitch jack rides ext0/ext1, and the
    # OFFSET/ATTEN correction folds into the const (cv_const_mult).  Both are
    # no-ops -- ext left unset, mult 1.0 -- when CV is disabled or in gate mode,
    # so this line changes nothing for a MIDI-only setup.
    e0, e1 = cv_pitch_coefs()
    if e0:
        c[C_EXT0] = e0
    if e1:
        c[C_EXT1] = e1
    const *= cv_const_mult()
    # A freq const of 0 is ZERO_HZ_LOG_VAL (silence), not "no offset".
    c[C_CONST] = max(1.0, const)
    return coef_str(c)


def osc_duty_coefs(which, v):
    """duty for OSC A or B -- i.e. WAVETABLE POSITION.

    `duty` is what crossfades across the 64 cycles of a wavetable preset
    (oscillators.c render_wavetable), and it is a full coefficient list, so
    position scanning is modulated inside AMY's DSP at no MicroPython cost.
    This is the single most important line in the whole synth."""
    const = P[which + "_pos"] + voice_pos_offset(v)
    c = [None] * NCOEF
    const = _apply_routings(c, which + "_pos", const, 'lin')
    # AMY clamps the interpolation itself, but keeping the const in range means
    # the modulation swings around a position that is actually on the table.
    c[C_CONST] = clamp(const, 0.0, 1.0)
    return coef_str(c)


def osc_amp_coefs(which):
    """amp for OSC A or B.

    Coefficients: const gain, note, vel, eg0 (the amp envelope), plus any
    routings.  The vel coefficient is velocity SENSITIVITY, not a gain -- amp
    coefs combine in a log domain where a full-velocity note contributes 0
    whatever the coef is, so lowering it lifts SOFT notes toward full while
    leaving hard hits untouched."""
    c = [None] * NCOEF
    c[C_CONST] = clamp(P[which + "_lvl"], 0.0, 1.0)
    c[C_VEL] = clamp(P["vsens"], 0.0, 1.0)
    c[C_EG0] = 1.0
    _apply_routings(c, which + "_lvl", 0.0, 'amp')
    return coef_str(c)


def _eff_osc_drive(which):
    """Effective per-osc drive.  Folding only bites once the signal exceeds
    +/-1, but an oscillator sits below that (amp ~0.8), so with FOLD on we lift
    drive to a minimum that actually reaches the fold threshold -- otherwise
    turning FOLD on with drive at 1 does nothing audible."""
    d = P[which + "_drv"]
    if P[which + "_fold"] and d < 2.0:
        d = 2.0
    return d


def osc_drive_coefs(which):
    """dist_drive for OSC A or B: the per-oscillator drive / wavefold depth.

    api.md: the const is LINEAR drive (1/16..16), and the modulation coefs are
    OCTAVES of it.  dist_drive is shared by whichever stages are enabled, so
    this is both the saturator's drive and the wavefolder's fold depth."""
    c = [None] * NCOEF
    const = _apply_routings(c, which + "_drv", _eff_osc_drive(which), 'oct')
    c[C_CONST] = clamp(const, 0.0625, 16.0)
    return coef_str(c)


def head_filter_coefs():
    """filter_freq on the SILENT head -- one filter across the summed voice.

    The const is Hz; note (keyboard tracking), vel and every modulation term
    add OCTAVES on top.  AMY does not clamp the sum, so the const is pulled
    down until the worst case stays under FILT_CEILING.  The knob still reads
    what you set; only the sum is limited."""
    # Worst-case upward modulation, in octaves.  Keyboard tracking is NOT
    # fkbd octaves: the note term is scaled by the note's own log-frequency
    # relative to A4, so at MIDI 127 a tracking of 1.0 is (127-69)/12 = 4.83
    # octaves.  Under-counting that is how a "safe" cutoff still rings at the
    # top of the keyboard.
    kbd_oct = P["fkbd"] * ((127.0 - 69.0) / 12.0)
    up = _up_octaves("cut", kbd_oct + P["fvel"])
    const = clamp(P["cutoff"], 20.0, FILT_CEILING)
    c = [None] * NCOEF
    c[C_NOTE] = P["fkbd"]
    c[C_VEL] = P["fvel"]
    const = _apply_routings(c, "cut", const, 'oct')
    const = clamp(const, 20.0, FILT_CEILING)

    # Pull the const down first -- that keeps the modulation depth you dialled
    # in, and is enough for any sane patch.
    if up > 0.0:
        ceiling = FILT_CEILING / (2.0 ** up)
        if const > ceiling:
            const = max(20.0, ceiling)
        # If even the 20 Hz floor cannot absorb it, the modulation itself is
        # asking to go past Nyquist, so scale the terms down until the worst
        # case lands exactly on FILT_CEILING.  A resonant biquad driven past
        # Nyquist goes unstable and rings at a fixed pitch on every note; a
        # slightly shallower sweep is the better failure.
        allowed = math.log(FILT_CEILING / const) / math.log(2.0)
        if up > allowed:
            scale = max(0.0, allowed / up)
            c[C_NOTE] = P["fkbd"] * scale
            c[C_VEL] = P["fvel"] * scale
            for i in (C_EG0, C_EG1, C_MOD0, C_MOD1):
                if c[i]:
                    c[i] = c[i] * scale
    c[C_CONST] = const
    return coef_str(c)


def head_drive_coefs():
    c = [None] * NCOEF
    const = _apply_routings(c, "f_drv", P["fdrv"], 'oct')
    c[C_CONST] = clamp(const, 0.0625, 16.0)
    return coef_str(c)


def head_pan_coefs(v):
    """pan on the head -- the VOICE's pan.

    Per-osc pan inside a chain is inert: AMY pans the whole collected chain
    buffer once, through the head (verified in the Megatron build).  With one
    synth per voice that is exactly what we want -- this is the unison stack's
    stereo spread, and it is only reachable because of the four-synth layout."""
    c = [None] * NCOEF
    const = _apply_routings(c, "pan", voice_pan(v), 'lin')
    c[C_CONST] = clamp(const, 0.0, 1.0)
    return coef_str(c)


# ---- envelopes ------------------------------------------------------------
#  Every envelope here is an AMY breakpoint set.  Nothing is stepped from
#  Python -- the brief's "use AMY's own envelope functionality rather than
#  calculating envelopes continuously in MicroPython", and the reason the main
#  loop can stay at UI rate.
#
#  Breakpoint format: time_ms,value pairs, the LAST pair being the release
#  (which triggers on note-off).  So "A,1,D,S,R,0" is a standard ADSR.

def adsr_bp(a, d, s, r):
    return "%d,1,%d,%.3f,%d,0" % (int(a), int(d), clamp(s, 0.0, 1.0), int(r))


def amp_bp():
    return adsr_bp(P["aa"], P["ad"], P["as"], P["ar"])


def mod3_bp():
    return adsr_bp(P["m3_a"], P["m3_d"], P["m3_s"], P["m3_r"])


def mod4_bp():
    return adsr_bp(P["m4_a"], P["m4_d"], P["m4_s"], P["m4_r"])


# --------------------------------------------------------------------------
#  SECTION 5 : LFOs / MODULATORS  (MOD1 and MOD2, one pair per voice)
# --------------------------------------------------------------------------
#  These are ordinary AMY oscillators named as another osc's `mod_source`, at
#  which point AMY silences them and routes their output into the mod0 / mod1
#  coefficient slots.  Every voice carries its own pair, which costs nothing
#  (they are silent) and buys the per-voice modulation variation that makes a
#  unison stack sound like four oscillators rather than one loud one.
#
#  HARD CONSTRAINT, verified in src/amy.c: an osc with role SYNTH_IS_MOD_SOURCE
#  is SKIPPED by both the note-on and the note-off handler (amy.c:1921, :1983).
#  So a mod oscillator:
#    * can never carry an envelope (its EGs would never be triggered), which is
#      why its amp is a bare constant with vel and eg0 explicitly ZEROED -- the
#      AMY default amp coefs are 1,0,1,1, and leaving eg0 at 1 on an osc that
#      never gets a note-on would hold the modulator at zero forever; and
#    * cannot be note-retriggered with a note event -- TRIG instead re-sends
#      `phase`, which is a plain parameter message and warps the running phase.

def mod_rate_hz(n):
    """LFO rate for MOD n (1 or 2), honouring tempo sync."""
    div = int(clamp(P["m%d_div" % n], 0, len(SYNC_BEATS) - 1))
    beats = SYNC_BEATS[div]
    if div > 0 and beats > 0.0:
        return clamp((P["tempo"] / 60.0) / beats, 0.01, 100.0)
    return clamp(P["m%d_rate" % n], 0.01, 100.0)


def mod_freq_coefs(n):
    """freq for MOD n.

    LFO mode is an ABSOLUTE frequency, so `note` and `bend` are explicitly
    zeroed -- AMY's default freq coefs are 0,1,0,0,0,0,1 and leaving them would
    make the LFO track the keyboard.  AUDIO mode does the opposite: the const
    becomes REF_HZ * ratio and note/bend go back to 1, turning the modulator
    into an FM/RM operator that tracks the played note."""
    c = [None] * NCOEF
    if P["m%d_mode" % n] == 1:          # AUDIO -- an FM / ring-mod operator
        c[C_CONST] = max(1.0, REF_HZ * clamp(P["m%d_ratio" % n], 0.01, 32.0))
        c[C_NOTE] = 1.0
        c[C_BEND] = 1.0
    else:                                # LFO -- free-running, absolute Hz
        c[C_CONST] = mod_rate_hz(n)
        c[C_NOTE] = 0.0
        c[C_VEL] = 0.0
        c[C_EG0] = 0.0
        c[C_EG1] = 0.0
        c[C_MOD0] = 0.0
        c[C_BEND] = 0.0
    return coef_str(c)


def mod_amp_coefs(n):
    """amp for MOD n -- the modulation DEPTH, and nothing else.

    vel and eg0 are forced to 0 for the reason in the section note above: this
    oscillator will never receive a note event, so any envelope term would pin
    it at silence."""
    c = [None] * NCOEF
    c[C_CONST] = clamp(P["m%d_depth" % n], 0.0, 1.0)
    c[C_NOTE] = 0.0
    c[C_VEL] = 0.0
    c[C_EG0] = 0.0
    return coef_str(c)


# --------------------------------------------------------------------------
#  SECTION 6 : VOICE CONSTRUCTION
# --------------------------------------------------------------------------
_drift_cents = [0.0] * NVOICE       # slow analogue wander, written by service_drift()


def _stage_needed(prefix, drv_key, fold_key):
    """Whether an oscillator's distortion block has to be switched on at all.

    An always-on soft clipper colours the sound even at unity drive, so the
    stages are enabled only when the patch actually asks for them -- including
    the case where drive sits at 1 but a MOD routing pushes it up."""
    if P[fold_key]:
        return True
    if P[drv_key] > 1.001:
        return True
    for slot in range(NMOD):
        if mx_get(slot, prefix + "_drv") != 0.0:
            return True
    return False


def _send_osc_wt(sy, v, which, osc, chain_to, full):
    """Configure one wavetable oscillator (OSC A or OSC B)."""
    idx = int(P[which + "_wt"])
    kw = {"synth": sy, "osc": osc}
    if WT_ENABLED:
        kw["wave"] = W_WAVETABLE
        kw["preset"] = wt_preset_or_fallback(idx)
    else:
        # No -DAMY_WAVETABLE in this firmware: keep every other feature alive
        # on a plain oscillator rather than rendering silence.
        kw["wave"] = WT_FALLBACK_WAVE
    kw["freq"] = osc_freq_coefs(which, v)
    kw["duty"] = osc_duty_coefs(which, v)
    kw["amp"] = osc_amp_coefs(which)
    # mod_source is VOICE-RELATIVE inside a synth (docs/synth.md Note 3): these
    # are osc numbers within this voice, not absolute.  First entry feeds mod0,
    # second feeds mod1.
    kw["mod_source"] = [MOD1_OSC, MOD2_OSC]
    kw["portamento"] = int(P["glide"])
    if chain_to is not None:
        kw["chained_osc"] = chain_to
    # The oscillators never filter their own slice -- that would happen BEFORE
    # the sum reaches the head, i.e. the filter would run twice.
    kw["filter_type"] = 0
    if HAVE_DIST:
        on = _stage_needed(which, which + "_drv", which + "_fold")
        kw["dist_clip"] = 1 if on else 0
        kw["dist_fold"] = 1 if (on and P[which + "_fold"]) else 0
        if on:
            kw["dist_drive"] = osc_drive_coefs(which)
    if full:
        kw["bp0"] = amp_bp()            # eg0 = amp envelope
        kw["bp1"] = mod3_bp()           # eg1 = MOD3, the free assignable envelope
        kw["eg0_type"] = int(P["acurve"])
        kw["eg1_type"] = int(P["m3_curve"])
        # `phase` warps the RUNNING phase as well as arming the retrigger
        # phase, so it is only ever sent on a full rebuild -- sending it on a
        # knob turn clicks every held note.
        if P["phsync"]:
            kw["phase"] = "%.3f" % voice_phase(v, P[which + "_phase"])
    _amy_send(**kw)


def _send_head(sy, v, full):
    """The SILENT head: the voice's filter, drive, pan and MOD4 envelope.

    SILENT is what makes a voice-wide filter possible at all -- a sounding
    chain head filters only its own buffer, while a silent one is processed
    after the chain has been summed."""
    kw = {"synth": sy, "osc": HEAD,
          "wave": W_SILENT,
          # Unity pass-through, and deliberately NO envelope and NO velocity:
          # render_envelope() runs on the SUMMED chain for a silent osc, so an
          # envelope here would stack a second VCA over the whole voice.
          "amp": "1,0,0,0",
          "chained_osc": OSC_A,
          "mod_source": [MOD1_OSC, MOD2_OSC],
          "pan": head_pan_coefs(v),
          "filter_type": int(P["ftype"]),
          "resonance": round(clamp(P["reso"], 0.5, 16.0), 3),
          "filter_freq": head_filter_coefs(),
          "portamento": int(P["glide"])}
    if HAVE_DIST:
        hon = P["fdrv"] > 1.001 or any(mx_get(s, "f_drv") != 0.0
                                       for s in range(NMOD))
        kw["dist_clip"] = 1 if hon else 0
        if hon:
            kw["dist_drive"] = head_drive_coefs()
            kw["dist_mix"] = "%.3f" % clamp(P["fmix"], 0.0, 1.0)
    if full:
        kw["bp1"] = mod4_bp()           # eg1 = MOD4 = the filter envelope
        kw["eg1_type"] = int(P["m4_curve"])
    _amy_send(**kw)


def _send_mod_osc(sy, n, osc, full):
    kw = {"synth": sy, "osc": osc,
          "wave": LFO_WAVE[int(clamp(P["m%d_shape" % n], 0, len(LFO_WAVE) - 1))],
          "freq": mod_freq_coefs(n),
          "amp": mod_amp_coefs(n),
          "filter_type": 0}
    if full:
        kw["phase"] = "%.3f" % clamp(P["m%d_phase" % n], 0.0, 1.0)
    _amy_send(**kw)


def build_voice(v, full=False):
    """(Re)configure one voice.

    full=True reallocates the synth, which resets every oscillator -- boot,
    PANIC and patch load only.  A parameter change takes the cheap path and
    never touches allocation, envelopes or phase, which is what keeps a knob
    turn from clicking or re-triggering a held note."""
    sy = VOICE_SYNTHS[v]
    if full:
        # Release first, exactly as the Megatron build does: reallocating a
        # synth that still holds live voices is the kind of thing a C-level
        # allocator handles badly when it is not expecting it.
        _amy_send(synth=sy, num_voices=0)
        _amy_send(synth=sy, num_voices=1, oscs_per_voice=OSCS_PER_VOICE, bus=BUS)
        _amy_send(synth=sy, synth_level=1.0)
        # This sketch dispatches MIDI itself (channel filtering, voice modes,
        # unison), so AMY must not also grab notes for these synths.
        _amy_send(synth=sy, grab_midi_notes=0)
    # Order matters on a full build: the mod oscs must exist before anything
    # names them as a mod_source, or the role assignment has nothing to mark.
    _send_mod_osc(sy, 1, MOD1_OSC, full)
    _send_mod_osc(sy, 2, MOD2_OSC, full)
    _send_osc_wt(sy, v, "a", OSC_A, OSC_B, full)
    _send_osc_wt(sy, v, "b", OSC_B, None, full)
    _send_head(sy, v, full)


def build_all(full=False):
    for v in range(NVOICE):
        build_voice(v, full)


# --------------------------------------------------------------------------
#  SECTION 7 : TARGETED PARAMETER APPLICATION
# --------------------------------------------------------------------------
#  Every UI row names an apply GROUP, and each group resends only the handful
#  of messages that its parameters can possibly affect.  This is the brief's
#  "prevent parameter changes and UI activity from causing audio dropouts":
#  turning CUTOFF sends 4 messages (one head per voice), not a rebuild of 20
#  oscillators, and it never touches envelopes, phase or allocation -- so a
#  held note keeps sustaining exactly as it was.

def apply_osc_a():
    for v in range(NVOICE):
        _send_osc_wt(VOICE_SYNTHS[v], v, "a", OSC_A, OSC_B, False)


def apply_osc_b():
    for v in range(NVOICE):
        _send_osc_wt(VOICE_SYNTHS[v], v, "b", OSC_B, None, False)


def apply_head():
    for v in range(NVOICE):
        _send_head(VOICE_SYNTHS[v], v, False)


def apply_mod1():
    for v in range(NVOICE):
        _send_mod_osc(VOICE_SYNTHS[v], 1, MOD1_OSC, False)


def apply_mod2():
    for v in range(NVOICE):
        _send_mod_osc(VOICE_SYNTHS[v], 2, MOD2_OSC, False)


def apply_matrix():
    """A routing can reach any of the three scopes, so all three get resent."""
    apply_osc_a()
    apply_osc_b()
    apply_head()


def apply_unison():
    """Detune / width / position spread are per-voice, so this is the one
    group that genuinely differs voice to voice."""
    apply_matrix()


def apply_env():
    """Envelopes are resent to every osc that owns one.

    Deliberately NOT folded into the cheap path: bulk-resending breakpoints on
    every knob turn is what made notes sustain forever in an earlier AMYboard
    build, so envelopes move only when an envelope row is actually turned."""
    ab = amp_bp()
    m3 = mod3_bp()
    m4 = mod4_bp()
    for v in range(NVOICE):
        sy = VOICE_SYNTHS[v]
        for osc in (OSC_A, OSC_B):
            _amy_send(synth=sy, osc=osc, bp0=ab, bp1=m3,
                     eg0_type=int(P["acurve"]), eg1_type=int(P["m3_curve"]))
        _amy_send(synth=sy, osc=HEAD, bp1=m4, eg1_type=int(P["m4_curve"]))


def apply_fx():
    """AMY's own bus effects.  All of it runs in AMY's C DSP -- the brief's
    "use the built in AMY FX to save on cpu" -- so there is no custom C slot in
    this synth at all, unlike the Megatron build's CHARACTER/Clouds pair."""
    # Distortion runs FIRST in the bus chain, before EQ / chorus / echo /
    # reverb (api.md).  At bus scope only the const term of a coef list is
    # used, so these are plain numbers.  Only if this AMY build has it -- the
    # DRIVE page is otherwise inert rather than crashing the send.
    if HAVE_DIST:
        _amy_send(bus=BUS, dist_clip=1 if P["d_clip"] else 0)
        _amy_send(bus=BUS, dist_fold=1 if P["d_fold"] else 0)
        if int(P["d_bits"]) < 24 or int(P["d_rate"]) > 1:
            _amy_send(bus=BUS, dist_crush=[int(P["d_bits"]), int(P["d_rate"])])
        else:
            _amy_send(bus=BUS, dist_crush="0")
        _amy_send(bus=BUS, dist_drive="%.3f" % clamp(P["d_drive"], 0.0625, 16.0))
        _amy_send(bus=BUS, dist_mix="%.3f" % clamp(P["d_mix"], 0.0, 1.0))
    _amy_send(bus=BUS, eq="%.2f,%.2f,%.2f" % (P["eq_l"], P["eq_m"], P["eq_h"]))
    # chorus: level, max_delay (samples), lfo freq (Hz), depth
    _amy_send(bus=BUS, chorus="%.3f,%d,%.3f,%.3f"
             % (P["ch_lvl"], int(P["ch_dly"]), P["ch_rate"], P["ch_dep"]))
    # echo: level, delay_ms, max_delay_ms, feedback, filter_coef
    # max_delay is fixed at the ceiling of the ECHO MS range: AMY allocates the
    # echo line from it, so it must not shrink under a live delay time.
    _amy_send(bus=BUS, echo="%.3f,%d,%d,%.3f,%.3f"
             % (P["ec_lvl"], int(P["ec_ms"]), 1000, P["ec_fb"], P["ec_tone"]))
    # reverb: level, liveness, damping, xover Hz
    _amy_send(bus=BUS, reverb="%.3f,%.3f,%.3f,%.1f"
             % (P["rv_lvl"], P["rv_live"], P["rv_damp"], P["rv_xover"]))


def apply_sys():
    _amy_send(bus=BUS, volume=round(clamp(P["vol"], 0.0, 10.0), 3))
    if int(P["panic"]):
        P["panic"] = 0
        panic()


def apply_mode():
    """Voice mode changed.

    Nothing is allocated or freed -- the four synths already exist.  All that
    changes is which voices get sent a note, plus a resend of the per-voice
    coefficients, because detune / pan / position spread apply in UNISON and
    collapse to zero in MONO and POLY."""
    all_off()
    apply_matrix()


def apply_ab():
    apply_osc_a()
    apply_osc_b()


def apply_rebuild():
    """A full reallocation.  Cuts held notes, and is only reached by the few
    controls that genuinely cannot take effect any other way -- PH.SYNC (AMY
    has no command to un-set a trigger_phase) and the per-oscillator start
    phases it arms.

    Does NOT re-arm the gate: cv_trigger is a SYNTH-scoped mapping, not part of
    an oscillator, so rebuilding the oscillators leaves it untouched.  Re-arming
    here is what made turning PHASE / PH.SYNC / PH SPR retrigger the CV gate, so
    it is gone -- only amy.reset() (panic, boot) actually clears the mapping,
    and those re-arm explicitly."""
    all_off()
    build_all(full=True)


def apply_none():
    """Rows that only move UI state (the matrix cursor) or are serviced from
    loop() (DRIFT).  Nothing to send."""
    return


# --------------------------------------------------------------------------
#  CV ENGINE  (ported from megatron_v1, adapted to the 4-synth voice model)
# --------------------------------------------------------------------------
#  CV drives VOICE 0 -- its SILENT head takes the note, which AMY propagates
#  down the chain to OSC A/B, firing their envelopes exactly as a MIDI note
#  does.  A eurorack rig is monophonic, so one voice is the right amount; in
#  UNISON/POLY the other three voices remain available to MIDI.
CV_SYNTH = None                 # resolved to VOICE_SYNTHS[0] at first use
_cal_dirty = False


def _cv_synth():
    global CV_SYNTH
    if CV_SYNTH is None:
        CV_SYNTH = VOICE_SYNTHS[0]
    return CV_SYNTH


def _cv_send(what, **kwargs):
    # A malformed/unsupported send (e.g. older AMY without cv_trigger) can
    # never take down MIDI/menu handling.
    try:
        _amy_send(**kwargs)
    except Exception as e:
        print("CV %s send failed:" % what, e)


_cv_trigger_sig = None          # last-armed (clear,on,off) tuple; None = unknown


def _cv_forget():
    """Drop the cached gate signature so the NEXT setup_cv() re-arms for real.

    Call this whenever AMY's trigger list is wiped out from under us -- only
    amy.reset() does that (panic, boot) -- so the cache never claims a trigger
    is live when the engine has actually forgotten it."""
    global _cv_trigger_sig
    _cv_trigger_sig = None


def setup_cv():
    """Register the gate as a pair of AMY 'cv_trigger' mappings (audio-thread).

    One trigger per edge direction, each on its own hysteresis pair, because a
    single cv_trigger only fires in one direction.  The note is addressed to
    voice 0's HEAD -- a chained oscillator refuses notes, so the head is the
    only member that can take one, and it propagates the note down the chain.

    CRITICAL (gate retrigger fix): AMY's cv_trigger_new() APPENDS to a linked
    list -- sending a fresh trigger never replaces the old one, and the only way
    to remove a mapping is a bare 'ig<cv>' message (cv_trigger_clear_mappings).
    The old code re-sent the two full triggers on every call WITHOUT clearing,
    so each setup_cv() leaked two more gate mappings; after a few menu tweaks
    AMY held a stack of identical gate-ons that ALL fired on the next edge --
    heard as the gate retriggering.  So we now (1) CLEAR the gate CV first, then
    (2) add exactly two mappings, and (3) skip the whole thing when the template
    is unchanged, so an unrelated menu change never even re-arms the gate."""
    global _cv_trigger_sig
    if not CV_ENABLED:
        return
    sy = _cv_synth()
    note_off_msg = "i%dv%dl0" % (sy, HEAD)
    if CV_PITCH_MODE == 'gate':
        # Hand cv_trigger the pitch CV too, so AMY samples it at the gate edge
        # and substitutes the note for '%v'.  The sampled note is relative to
        # AMY note 69, hence the -69 and /12 converting our base note.
        note_on_msg = "i%dv%dl%gn%%v" % (sy, HEAD, CV_GATE_VEL)
        pitch_args = ",%d,%g,%g" % (CV_PITCH_INPUT, CV_PITCH_SCALE,
                                    (cv_base_note() - 69.0) / 12.0)
    else:
        # 'track': the note carries only the base pitch; the CV itself rides
        # the oscillators' ext freq coefficient continuously (cv_pitch_coefs).
        note_on_msg = "i%dv%dl%gn%g" % (sy, HEAD, CV_GATE_VEL, cv_base_note())
        pitch_args = ""
    on_msg = "%d,%g,%g%s,%s" % (CV_GATE_INPUT, CV_GATE_ON, CV_GATE_OFF,
                               pitch_args, note_on_msg)
    # The note-off trigger never needs pitch args -- it only releases the voice.
    off_msg = "%d,%g,%g,%s" % (CV_GATE_INPUT, CV_GATE_OFF, CV_GATE_ON,
                              note_off_msg)
    sig = (sy, CV_GATE_INPUT, on_msg, off_msg)
    if sig == _cv_trigger_sig:
        return                       # gate already armed with this exact template
    # Clear the gate CV's existing mappings (bare 'ig<cv>') so we REPLACE, never
    # stack, then add the two fresh edges.
    _cv_send("gate-clear", synth=sy, cv_trigger="%d" % CV_GATE_INPUT)
    _cv_send("gate-on", synth=sy, cv_trigger=on_msg)
    _cv_send("gate-off", synth=sy, cv_trigger=off_msg)
    _cv_trigger_sig = sig


def push_cv_pitch():
    """Make the current OFFSET/SCALE audible RIGHT NOW.

    The SCALE lives on the oscillators' ext freq coefficient and the OFFSET on
    the const; retune() re-pushes both to every voice, and setup_cv() re-arms
    the gate template so a change lands before the next gate too."""
    setup_cv()
    retune()


def save_cv_cal():
    """Persist the calibration.  Never raises -- flash faults must not disturb
    audio or MIDI."""
    try:
        with open(CV_CAL_FILE, "w") as f:
            json.dump({"offset": CV_PITCH_OFFSET_V, "coarse": CV_PITCH_COARSE_V,
                       "gate_on": CV_GATE_ON, "base": CV_BASE_NOTE}, f)
        return True
    except Exception as e:
        print("cv cal write failed:", e)
        return False


def load_cv_cal():
    """Restore the calibration at boot.  A missing file is the normal first run."""
    global CV_PITCH_OFFSET_V, CV_PITCH_COARSE_V, CV_GATE_ON, CV_GATE_OFF
    global CV_BASE_NOTE
    try:
        with open(CV_CAL_FILE) as f:
            d = json.load(f)
    except Exception:
        return False
    if not isinstance(d, dict):
        return False
    try:
        CV_PITCH_OFFSET_V = float(d.get("offset", CV_PITCH_OFFSET_V))
        CV_PITCH_COARSE_V = float(d.get("coarse", CV_PITCH_COARSE_V))
        CV_GATE_ON = float(d.get("gate_on", CV_GATE_ON))
        CV_GATE_OFF = CV_GATE_ON * 0.5
        CV_BASE_NOTE = int(d.get("base", CV_BASE_NOTE))
    except Exception as e:
        print("cv cal load failed:", e)
        return False
    # Mirror the loaded constants into the page's P values.
    P["cvoff"] = CV_PITCH_OFFSET_V
    P["cvatt"] = CV_PITCH_COARSE_V
    P["cvgate"] = CV_GATE_ON
    P["cvnote"] = CV_BASE_NOTE
    return True


_cal_last_save = 0


def apply_cvcal():
    """CV CAL page handler.

    Every control is a plain live setting -- turn it, hear it.  The values read
    out of P into the module constants the CV engine uses, then push to AMY
    immediately.

    CV calibration is a GLOBAL, PERSISTENT setting: it describes this rig, not a
    sound, so it is never stored in a patch (see PATCH_SKIP) and it lives in its
    own file (CV_CAL_FILE).  To make sure it survives even if the app is closed
    right after a tweak, a change is written to flash promptly here (throttled
    so a knob sweep does not hammer the card), with a final flush on page
    change (cv_cal_save_if_dirty).

    #4 -- MINIMAL CV re-push so a calibration tweak never glitches the gate:
    the old code re-armed BOTH cv_trigger mappings (setup_cv) on every detent of
    every knob, which could disturb a held, in-tune note.  The trim (OFFSET /
    ATTEN) only rides the oscillator const in 'track' mode, so there a live
    retune() is enough and the gate is left untouched; only the values that
    actually change the trigger TEMPLATE (GATE V thresholds, 0V NOTE, and -- in
    'gate' mode only -- the trim that AMY bakes into the note) re-arm it.  The
    calibration numbers themselves are applied identically either way, so tuning
    is preserved exactly; this only removes needless gate re-arms."""
    global CV_PITCH_OFFSET_V, CV_PITCH_COARSE_V, CV_GATE_ON, CV_GATE_OFF
    global CV_BASE_NOTE, _cal_dirty, _cv_cal_msg, _cal_last_save
    off_changed = atten_changed = gate_changed = note_changed = False
    if CV_PITCH_OFFSET_V != P["cvoff"]:
        CV_PITCH_OFFSET_V = P["cvoff"]
        off_changed = True
    if CV_PITCH_COARSE_V != P["cvatt"]:
        CV_PITCH_COARSE_V = P["cvatt"]
        atten_changed = True
    if CV_GATE_ON != P["cvgate"]:
        CV_GATE_ON = P["cvgate"]
        CV_GATE_OFF = CV_GATE_ON * 0.5   # release follows at half; one knob
        gate_changed = True
    if CV_BASE_NOTE != int(P["cvnote"]):
        CV_BASE_NOTE = int(P["cvnote"])
        note_changed = True
    if not (off_changed or atten_changed or gate_changed or note_changed):
        return
    _cv_cal_msg = "trim %+.2fV" % cv_offset_volts()

    # The trim rides the oscillator const in 'track' mode (cv_const_mult) and the
    # note template in 'gate' mode (cv_base_note); GATE V and 0V NOTE always live
    # in the trigger template.  Re-arm the gate ONLY when the template actually
    # moved; otherwise just retune the live oscillators.
    trim_changed = off_changed or atten_changed
    need_gate = gate_changed or note_changed or (trim_changed
                                                 and CV_PITCH_MODE == 'gate')
    need_retune = trim_changed and CV_PITCH_MODE == 'track'
    if need_gate:
        setup_cv()          # thresholds / note template changed -> re-arm
    if need_retune:
        retune()            # trim rides the const -> correct held pitch live

    _cal_dirty = True
    now = _now()
    if _dt(now, _cal_last_save) > 1000:          # at most ~1 write/second
        if save_cv_cal():
            _cal_dirty = False
        _cal_last_save = now


def cv_cal_save_if_dirty():
    """Flush a changed calibration to flash.  Called on page change, so the last
    value of a sweep is always persisted even if the throttle skipped it."""
    global _cal_dirty
    if _cal_dirty:
        save_cv_cal()
        _cal_dirty = False




APPLY = {
    "a": apply_osc_a, "b": apply_osc_b, "head": apply_head,
    "ab": apply_ab, "rebuild": apply_rebuild, "none": apply_none,
    "m1": apply_mod1, "m2": apply_mod2, "mx": apply_matrix,
    "env": apply_env, "fx": apply_fx, "sys": apply_sys,
    "uni": apply_unison, "mode": apply_mode, "cvcal": apply_cvcal,
}


def apply_group(group):
    fn = APPLY.get(group)
    if fn:
        try:
            fn()
        except Exception as e:
            print("apply", group, "failed:", e)


# --------------------------------------------------------------------------
#  APPLY COALESCING  --  one AMY flush per loop tick, not one per encoder detent
# --------------------------------------------------------------------------
#  An encoder sweep fires edit_row() on every detent.  Applying each one on the
#  spot floods the audio thread (a UNISON detune is 12 sends -- turn it fast and
#  a single 60 ms tick can carry dozens).  Instead each edit only MARKS its
#  apply group dirty; service_apply() flushes the accumulated set ONCE per tick
#  from loop().  N detents of the same knob in a tick then cost one apply, and
#  the note/gate state a held voice sees is refreshed once, cleanly, per frame.
#
#  Note events (note_on/off), MIDI CCs and one-shot click actions still apply
#  immediately -- only the continuous encoder path is coalesced.
_apply_dirty = set()

# When two knobs move in the same tick, an expensive note-cutting group
# subsumes the cheap per-osc groups it already resends, so a rebuild never runs
# on top of (and re-cuts the notes of) an apply_osc_a queued alongside it.
_SUBSUMES = {
    "rebuild": {"rebuild", "mode", "uni", "mx", "ab", "a", "b", "head",
                "m1", "m2", "env"},
    "mode":    {"mode", "uni", "mx", "ab", "a", "b", "head"},
    "uni":     {"uni", "mx", "ab", "a", "b", "head"},
    "mx":      {"mx", "uni", "ab", "a", "b", "head"},
    "ab":      {"ab", "a", "b"},
}


def mark_apply(group):
    """Queue an apply group for the next service_apply() flush."""
    if group and group != "none":
        _apply_dirty.add(group)


def service_apply():
    """Flush all apply groups marked dirty this tick, coalesced.  Called from
    loop() right after input, so the frame that draws already reflects it."""
    if not _apply_dirty:
        return
    groups = set(_apply_dirty)
    _apply_dirty.clear()
    # Run at most one of the note-cutting supergroups, drop what it covers.
    for boss in ("rebuild", "mode", "uni", "mx", "ab"):
        if boss in groups:
            apply_group(boss)
            groups -= _SUBSUMES[boss]
            break
    # Everything left is independent (head, env, fx, sys, cvcal, m1, m2, ...).
    for g in groups:
        apply_group(g)


# --------------------------------------------------------------------------
#  SECTION 8 : VOICE ALLOCATION AND NOTE HANDLING
# --------------------------------------------------------------------------
#  Three modes, one allocator, zero AMY object churn between them.
#
#  A note is sent to a voice's HEAD ONLY.  AMY walks the chain from there and
#  writes the note into OSC A and OSC B itself -- which is exactly why per-osc
#  notes cannot be used for detune, and why every pitch offset lives in a freq
#  coefficient instead.

held = []                       # MIDI note stack, last-note priority (MONO)
_vnote = [None] * NVOICE        # note currently sounding on each voice
_vage = [0] * NVOICE            # allocation order, for stealing
_alloc_clock = 0
_cur_vel = 0.0


def _voice_note_on(v, note, vel, retrigger=True):
    sy = VOICE_SYNTHS[v]
    n = clamp(note, 0, 127)
    if retrigger:
        # Retrigger the two mod oscillators' phase if asked.  This has to be a
        # `phase` parameter message, not a note event: a mod-source osc ignores
        # note events entirely (see the SECTION 5 note).
        for n_mod, osc in ((1, MOD1_OSC), (2, MOD2_OSC)):
            if P["m%d_trig" % n_mod]:
                _amy_send(synth=sy, osc=osc,
                         phase="%.3f" % clamp(P["m%d_phase" % n_mod], 0.0, 1.0))
        _amy_send(synth=sy, osc=HEAD, note=round(n, 3), vel=round(vel, 4))
    else:
        # Pitch-only: portamento applies and nothing re-triggers.
        _amy_send(synth=sy, osc=HEAD, note=round(n, 3))
    _vnote[v] = note


def _voice_note_off(v):
    if _vnote[v] is None:
        return
    _amy_send(synth=VOICE_SYNTHS[v], osc=HEAD, vel=0)
    _vnote[v] = None


def _claim_voice(note):
    """Pick a voice for a new POLY note.

    Free voices first, then the OLDEST sounding one -- the conventional and
    least surprising steal.  A note already sounding on a voice reuses that
    voice, so a repeated note never doubles up."""
    global _alloc_clock
    _alloc_clock += 1
    for v in range(NVOICE):
        if _vnote[v] == note:
            _vage[v] = _alloc_clock
            return v
    for v in range(NVOICE):
        if _vnote[v] is None:
            _vage[v] = _alloc_clock
            return v
    oldest, best = 0, _vage[0]
    for v in range(1, NVOICE):
        if _vage[v] < best:
            oldest, best = v, _vage[v]
    _voice_note_off(oldest)
    _vage[oldest] = _alloc_clock
    return oldest


def note_on(note, vel):
    global _cur_vel
    _cur_vel = vel
    mode = int(P["vmode"])
    if note in held:
        held.remove(note)
    held.append(note)
    if mode == VM_MONO:
        # Legato: while another key is already down, glide to the new note
        # without retriggering the envelopes.  With GLIDE at 0 that is an
        # instant, click-free pitch change; above 0 it is portamento.
        legato = len(held) > 1
        _voice_note_on(0, note, vel, retrigger=not legato)
    elif mode == VM_UNISON:
        legato = len(held) > 1
        for v in range(NVOICE):
            _voice_note_on(v, note, vel, retrigger=not legato)
    else:
        v = _claim_voice(note)
        _voice_note_on(v, note, vel, retrigger=True)


def note_off(note):
    mode = int(P["vmode"])
    if note in held:
        held.remove(note)
    if mode == VM_POLY:
        for v in range(NVOICE):
            if _vnote[v] == note:
                _voice_note_off(v)
        return
    voices = [0] if mode == VM_MONO else list(range(NVOICE))
    if held:
        # Fall back to the note still held underneath, without retriggering.
        for v in voices:
            _voice_note_on(v, held[-1], _cur_vel, retrigger=False)
    else:
        for v in voices:
            _voice_note_off(v)


def all_off():
    del held[:]
    for v in range(NVOICE):
        _voice_note_off(v)


def retune():
    """Pitch-only refresh: detune / drift / mode changes land here.

    Never retriggers, so a held unison stack can be detuned live."""
    for v in range(NVOICE):
        sy = VOICE_SYNTHS[v]
        _amy_send(synth=sy, osc=OSC_A, freq=osc_freq_coefs("a", v))
        _amy_send(synth=sy, osc=OSC_B, freq=osc_freq_coefs("b", v))


def panic():
    """The one place besides boot that is allowed to reset AMY."""
    all_off()
    amy.reset()
    _cv_forget()        # reset() wiped the gate mappings -> force a real re-arm
    boot_amy()
    build_all(full=True)
    apply_fx()
    apply_sys()
    setup_cv()


# --------------------------------------------------------------------------
#  SECTION 9 : PAGES  --  the parameter surface
# --------------------------------------------------------------------------
#  Row: (LABEL, key, lo, hi, step, kind, apply-group)
#
#  A page may hold FEWER than 8 rows but never MORE: on the eight-encoder board
#  encoder N edits row N, so a 9th row would be physically unreachable.  boot()
#  checks this and complains loudly rather than stranding a parameter.
#
#  kinds: 'f' float  'i' int  'e' enum  'ms' time  'hz' frequency
#         'ct' cents  'a' momentary action  'wt' wavetable name
MOD_SLOT_NAMES = ["MOD1", "MOD2", "MOD3", "MOD4"]
WT_TARGETS = ["OSC A", "OSC B"]

ENUM_LISTS = {
    "vmode": VOICE_MODES, "ftype": FILTERS, "wt_src": WT_TARGETS,
    "a_fold": ONOFF, "b_fold": ONOFF, "phsync": ONOFF,
    "d_clip": ONOFF, "d_fold": ONOFF,
    "m1_shape": LFO_SHAPES, "m2_shape": LFO_SHAPES,
    "m1_mode": MOD_RATE_MODES, "m2_mode": MOD_RATE_MODES,
    "m1_pol": POLARITY, "m2_pol": POLARITY,
    "m3_pol": POLARITY, "m4_pol": POLARITY,
    "m1_div": SYNC_DIVS, "m2_div": SYNC_DIVS,
    "m1_trig": ONOFF, "m2_trig": ONOFF,
    "acurve": EG_CURVES, "m3_curve": EG_CURVES, "m4_curve": EG_CURVES,
    "mx_slot": MOD_SLOT_NAMES, "mx_dest": DEST_LABELS,
}

PAGES = [
    ("OSC A", [
        ("TABLE",  "a_wt",     0, 999,   1,    'wt', 'a'),
        ("POSITION", "a_pos",  0.0, 1.0, 0.02, 'f',  'a'),
        ("COARSE", "a_coarse", -24.0, 24.0, 1,  'i', 'a'),
        ("FINE",   "a_fine",   -50.0, 50.0, 1,  'ct', 'a'),
        ("LEVEL",  "a_lvl",    0.0, 1.0,  0.05, 'f', 'a'),
        ("DRIVE",  "a_drv",    1.0, 16.0, 0.25, 'f', 'a'),
        ("FOLD",   "a_fold",   0, 1,      1,    'e', 'a'),
        ("PHASE",  "a_phase",  0.0, 1.0,  0.05, 'f', 'rebuild'),
    ]),
    ("OSC B", [
        ("TABLE",  "b_wt",     0, 999,   1,    'wt', 'b'),
        ("POSITION", "b_pos",  0.0, 1.0, 0.02, 'f',  'b'),
        ("COARSE", "b_coarse", -24.0, 24.0, 1,  'i', 'b'),
        ("FINE",   "b_fine",   -50.0, 50.0, 1,  'ct', 'b'),
        ("LEVEL",  "b_lvl",    0.0, 1.0,  0.05, 'f', 'b'),
        ("DRIVE",  "b_drv",    1.0, 16.0, 0.25, 'f', 'b'),
        ("FOLD",   "b_fold",   0, 1,      1,    'e', 'b'),
        ("PHASE",  "b_phase",  0.0, 1.0,  0.05, 'f', 'rebuild'),
    ]),
    # Load a user wavetable from the SD card.  The synth boots on its built-in
    # tables (INT 0..4) and never touches the card on its own -- this page is
    # the deliberate opt-in.  SCAN SD lists what is on the card, FILE browses
    # it, TARGET picks which oscillator, and LOAD commits the chosen file:
    # streaming it into RAM, adding it to the TABLE knob's catalogue and
    # selecting it on that oscillator.  Any .wav of >= 512 samples works
    # (shorepine/amy#997), so ordinary samples are fair game, not only
    # purpose-built tables.
    ("WT LOAD", [
        ("TARGET",  "wt_src",      0, 1,   1, 'e',  'none'),
        ("FILE",    "wt_browse",   0, 999, 1, 'sd', 'none'),
        ("LOAD",    "wt_load",     0, 1,   1, 'a',  'none'),
        ("SCAN SD", "wt_scan_act", 0, 1,   1, 'a',  'none'),
    ]),
    ("MIX", [
        ("VOICE",  "vmode",   0, 2,      1,    'e', 'mode'),
        ("GLIDE",  "glide",   0.0, 2000.0, 10, 'ms', 'ab'),
        ("VEL>AMP", "vsens",  0.0, 1.0,  0.05, 'f', 'ab'),
        # PH.SYNC cannot be a live toggle: AMY has no wire command to UN-set an
        # already-set trigger_phase, so turning it off needs fresh oscillators.
        ("PH.SYNC", "phsync", 0, 1,      1,    'e', 'rebuild'),
        ("BEND",   "bend",    0.0, 12.0, 1,    'f', 'sys'),
        ("MIDI CH", "mch",    1, 16,     1,    'i', 'sys'),
        ("VOLUME", "vol",     0.0, 8.0,  0.25, 'f', 'sys'),
        ("PANIC",  "panic",   0, 1,      1,    'a', 'sys'),
    ]),
    ("FILTER", [
        ("TYPE",   "ftype",   0, 6,      1,    'e', 'head'),
        ("CUTOFF", "cutoff",  30.0, 12000.0, 0, 'hz', 'head'),
        ("RESO",   "reso",    0.5, 16.0, 0.25, 'f', 'head'),
        # This row IS the MOD4 -> CUTOFF routing (see mx_get/mx_set): the
        # filter envelope and the fourth modulator are the same generator.
        ("ENV AMT", "fenv",  -4.0, 4.0,  0.15, 'f', 'head'),
        ("KBD TRK", "fkbd",   0.0, 1.0,  0.05, 'f', 'head'),
        ("VEL",    "fvel",    0.0, 1.0,  0.05, 'f', 'head'),
        ("DRIVE",  "fdrv",    1.0, 16.0, 0.25, 'f', 'head'),
        ("MIX",    "fmix",    0.0, 1.0,  0.05, 'f', 'head'),
    ]),
    # The AMP envelope.  The FILTER envelope is not duplicated here: it IS
    # MOD 4, which has its own full page (depth, curve, velocity, polarity),
    # and the FILTER page's ENV AMT row is the MOD4 -> CUTOFF routing.  One
    # generator, one place to edit it, no chance of two pages disagreeing.
    ("ENV", [
        ("AMP A",  "aa",  0.0, 4000.0, 10,   'ms', 'env'),
        ("AMP D",  "ad",  1.0, 8000.0, 10,   'ms', 'env'),
        ("AMP S",  "as",  0.0, 1.0,    0.05, 'f',  'env'),
        ("AMP R",  "ar",  1.0, 8000.0, 10,   'ms', 'env'),
        ("CURVE",  "acurve", 0, 3,     1,    'e',  'env'),
    ]),
    ("MOD 1", [
        ("SHAPE",  "m1_shape", 0, 5,     1,    'e', 'm1'),
        ("MODE",   "m1_mode",  0, 1,     1,    'e', 'm1'),
        # RATE follows MODE: Hz as an LFO, harmonic ratio as an FM/RM operator.
        # One row, because you only ever need one of the two (see eff_key()).
        ("RATE",   "m1_rate",  0.01, 20.0, 0.05, 'f', 'm1'),
        ("DEPTH",  "m1_depth", 0.0, 1.0,  0.05, 'f', 'm1'),
        ("PHASE",  "m1_phase", 0.0, 1.0,  0.05, 'f', 'm1'),
        ("SYNC",   "m1_div",   0, 7,      1,    'e', 'm1'),
        ("POLARITY", "m1_pol", 0, 1,      1,    'e', 'mx'),
        ("TRIG",   "m1_trig",  0, 1,      1,    'e', 'm1'),
    ]),
    ("MOD 2", [
        ("SHAPE",  "m2_shape", 0, 5,     1,    'e', 'm2'),
        ("MODE",   "m2_mode",  0, 1,     1,    'e', 'm2'),
        ("RATE",   "m2_rate",  0.01, 20.0, 0.05, 'f', 'm2'),
        ("DEPTH",  "m2_depth", 0.0, 1.0,  0.05, 'f', 'm2'),
        ("PHASE",  "m2_phase", 0.0, 1.0,  0.05, 'f', 'm2'),
        ("SYNC",   "m2_div",   0, 7,      1,    'e', 'm2'),
        ("POLARITY", "m2_pol", 0, 1,      1,    'e', 'mx'),
        ("TRIG",   "m2_trig",  0, 1,      1,    'e', 'm2'),
    ]),
    ("MOD 3", [
        ("ATTACK", "m3_a",  0.0, 4000.0, 10,   'ms', 'env'),
        ("DECAY",  "m3_d",  1.0, 8000.0, 10,   'ms', 'env'),
        ("SUSTAIN", "m3_s", 0.0, 1.0,    0.05, 'f',  'env'),
        ("RELEASE", "m3_r", 1.0, 8000.0, 10,   'ms', 'env'),
        ("CURVE",  "m3_curve", 0, 3,     1,    'e',  'env'),
        ("VEL",    "m3_vel", 0.0, 1.0,   0.05, 'f',  'mx'),
        ("POLARITY", "m3_pol", 0, 1,     1,    'e',  'mx'),
    ]),
    ("MOD 4", [
        ("ATTACK", "m4_a",  0.0, 4000.0, 10,   'ms', 'env'),
        ("DECAY",  "m4_d",  1.0, 8000.0, 10,   'ms', 'env'),
        ("SUSTAIN", "m4_s", 0.0, 1.0,    0.05, 'f',  'env'),
        ("RELEASE", "m4_r", 1.0, 8000.0, 10,   'ms', 'env'),
        ("CURVE",  "m4_curve", 0, 3,     1,    'e',  'env'),
        ("VEL",    "m4_vel", 0.0, 1.0,   0.05, 'f',  'mx'),
        ("POLARITY", "m4_pol", 0, 1,     1,    'e',  'mx'),
    ]),
    # The matrix is a 4 x 11 grid -- far more than eight encoders can hold, so
    # it is edited as a cursor (SLOT + DEST) plus one AMOUNT, with the whole
    # grid drawn live in the visual pane above.  Every routing is reachable and
    # nothing is hidden.
    ("MATRIX", [
        ("SLOT",   "mx_slot", 0, NMOD - 1,        1, 'e', 'none'),
        ("DEST",   "mx_dest", 0, len(DESTS) - 1,  1, 'e', 'none'),
        ("AMOUNT", "mx_amt", -4.0, 4.0,        0.05, 'f', 'mx'),
        ("CLEAR",  "mx_clr",  0, 1,               1, 'a', 'mx'),
        ("CLR ALL", "mx_clrall", 0, 1,            1, 'a', 'mx'),
    ]),
    ("UNISON", [
        ("DETUNE", "uni_det",   0.0, 50.0, 1,    'ct', 'uni'),
        ("WIDTH",  "uni_width", 0.0, 1.0,  0.05, 'f',  'uni'),
        ("POS SPR", "uni_pos",  0.0, 0.5,  0.02, 'f',  'uni'),
        ("PH SPR", "uni_phase", 0.0, 1.0,  0.05, 'f',  'rebuild'),
        ("DRIFT",  "uni_drift", 0.0, 1.0,  0.05, 'f',  'none'),
    ]),
    ("DRIVE", [
        ("DRIVE",  "d_drive", 1.0, 16.0, 0.25, 'f', 'fx'),
        ("CLIP",   "d_clip",  0, 1,      1,    'e', 'fx'),
        ("FOLD",   "d_fold",  0, 1,      1,    'e', 'fx'),
        ("BITS",   "d_bits",  1, 24,     1,    'i', 'fx'),
        ("RATE",   "d_rate",  1, 32,     1,    'i', 'fx'),
        ("MIX",    "d_mix",   0.0, 1.0,  0.05, 'f', 'fx'),
    ]),
    ("FX", [
        ("CHORUS", "ch_lvl",  0.0, 1.0,  0.05, 'f', 'fx'),
        ("CH DLY", "ch_dly",  1.0, 320.0, 10,  'i', 'fx'),
        ("CH RATE", "ch_rate", 0.05, 8.0, 0.05, 'f', 'fx'),
        ("CH DEPTH", "ch_dep", 0.0, 1.0, 0.05, 'f', 'fx'),
        ("ECHO",   "ec_lvl",  0.0, 1.0,  0.05, 'f', 'fx'),
        ("ECHO MS", "ec_ms",  20.0, 1000.0, 10, 'ms', 'fx'),
        ("ECHO FB", "ec_fb",  0.0, 0.9,  0.05, 'f', 'fx'),
        ("ECHO TONE", "ec_tone", -1.0, 1.0, 0.1, 'f', 'fx'),
    ]),
    ("REVERB", [
        ("LEVEL",  "rv_lvl",   0.0, 1.0,  0.05, 'f', 'fx'),
        ("LIVENESS", "rv_live", 0.0, 1.0, 0.02, 'f', 'fx'),
        ("DAMPING", "rv_damp", 0.0, 1.0,  0.05, 'f', 'fx'),
        ("XOVER",  "rv_xover", 200.0, 12000.0, 0, 'hz', 'fx'),
        ("EQ LOW", "eq_l",   -15.0, 15.0, 1,    'f', 'fx'),
        ("EQ MID", "eq_m",   -15.0, 15.0, 1,    'f', 'fx'),
        ("EQ HIGH", "eq_h",  -15.0, 15.0, 1,    'f', 'fx'),
        ("TEMPO",  "tempo",   40.0, 240.0, 1,   'f', 'm1'),
    ]),
    # Eurorack CV input, calibrated by ear.  CV1 = gate/trigger, CV2 = 1V/oct
    # pitch.  Turn OFFSET so 0V sounds the 0V NOTE, ATTEN for the last few
    # cents, GATE V to clear an unpatched jack's float.  The pane above shows
    # both jacks live and the note CV2 currently resolves to.
    ("CV CAL", [
        ("ATTEN",   "cvatt",  -2.0, 2.0, 0.20, 'f', 'cvcal'),
        ("OFFSET",  "cvoff",  -2.0, 2.0, 0.01, 'f', 'cvcal'),
        ("GATE V",  "cvgate",  0.2, 5.0, 0.1,  'f', 'cvcal'),
        ("0V NOTE", "cvnote",  0, 127,   1,    'i', 'cvcal'),
    ]),
]

# 4-character grid labels, keyed by parameter so a control that appears on two
# screens reads the same on both.
# Three-letter cell labels.  The focused parameter's FULL name and value are
# shown at the top of the page, so the cells only need a compact reminder.
SHORT = {
    "a_wt": "TAB", "a_pos": "POS", "a_coarse": "CRS", "a_fine": "FIN",
    "a_lvl": "LVL", "a_drv": "DRV", "a_fold": "FLD", "a_phase": "PHS",
    "b_wt": "TAB", "b_pos": "POS", "b_coarse": "CRS", "b_fine": "FIN",
    "b_lvl": "LVL", "b_drv": "DRV", "b_fold": "FLD", "b_phase": "PHS",
    "vmode": "VOI", "glide": "GLD", "vsens": "VEL", "phsync": "SYN",
    "bend": "BND", "mch": "MID", "vol": "VOL", "panic": "PNC",
    "wt_src": "DST", "wt_browse": "FIL", "wt_load": "LD", "wt_scan_act": "SCN",
    "ftype": "TYP", "cutoff": "CUT", "reso": "RES", "fenv": "ENV",
    "fkbd": "KBD", "fvel": "VEL", "fdrv": "DRV", "fmix": "MIX",
    "aa": "ATK", "ad": "DEC", "as": "SUS", "ar": "REL", "acurve": "CRV",
    "m1_shape": "SHP", "m1_mode": "MOD", "m1_rate": "RAT",
    "m1_ratio": "RTO", "m1_depth": "DEP", "m1_phase": "PHS",
    "m1_div": "SYN", "m1_pol": "POL", "m1_trig": "TRG",
    "m2_shape": "SHP", "m2_mode": "MOD", "m2_rate": "RAT",
    "m2_ratio": "RTO", "m2_depth": "DEP", "m2_phase": "PHS",
    "m2_div": "SYN", "m2_pol": "POL", "m2_trig": "TRG",
    "m3_a": "ATK", "m3_d": "DEC", "m3_s": "SUS", "m3_r": "REL",
    "m3_curve": "CRV", "m3_vel": "VEL", "m3_pol": "POL",
    "m4_a": "ATK", "m4_d": "DEC", "m4_s": "SUS", "m4_r": "REL",
    "m4_curve": "CRV", "m4_vel": "VEL", "m4_pol": "POL",
    "mx_slot": "SLT", "mx_dest": "DST", "mx_amt": "AMT",
    "mx_clr": "CLR", "mx_clrall": "CLA",
    "uni_det": "DTN", "uni_width": "WID", "uni_pos": "PSP",
    "uni_phase": "PHS", "uni_drift": "DRF",
    "d_drive": "DRV", "d_clip": "CLP", "d_fold": "FLD",
    "d_bits": "BIT", "d_rate": "RAT", "d_mix": "MIX",
    "ch_lvl": "CHO", "ch_dly": "CDL", "ch_rate": "CRT",
    "ch_dep": "CDP", "ec_lvl": "ECH", "ec_ms": "EMS",
    "ec_fb": "EFB", "ec_tone": "ETN",
    "rv_lvl": "RVB", "rv_live": "LIV", "rv_damp": "DMP",
    "rv_xover": "XOV", "eq_l": "EQL", "eq_m": "EQM", "eq_h": "EQH",
    "tempo": "BPM",
    "cvatt": "ATN", "cvoff": "OFF", "cvgate": "GAT", "cvnote": "0VN",
}


def eff_key(key):
    """The parameter a row actually edits right now.

    Only the MOD RATE rows are context-sensitive: as an LFO the row is a rate
    in Hz, and as an FM/RM operator it is a harmonic ratio.  They are different
    parameters with different ranges, so the row switches which one it points
    at rather than trying to be both at once."""
    if key == "m1_rate" and P["m1_mode"] == 1:
        return "m1_ratio"
    if key == "m2_rate" and P["m2_mode"] == 1:
        return "m2_ratio"
    return key


def eff_row(row):
    """`row` with its key (and range/label) swapped for the effective one."""
    label, key, lo, hi, step, kind, group = row
    k = eff_key(key)
    if k == key:
        return row
    return ("RATIO", k, 0.25, 16.0, 0.25, 'f', group)


# --------------------------------------------------------------------------
#  SECTION 10 : VALUE FORMATTING AND EDITING
# --------------------------------------------------------------------------

def fmt_value(key, kind, v):
    if kind == 'a':
        return "GO"
    if kind == 'wt':
        return wt_name(v)
    if kind == 'sd':
        return _sd_name(v)
    if kind == 'e':
        lst = ENUM_LISTS.get(key)
        if lst:
            return lst[int(clamp(int(v), 0, len(lst) - 1))]
        return str(int(v))
    if kind == 'i':
        return str(int(v))
    if kind == 'ms':
        if v >= 1000:
            return "%.1fs" % (v / 1000.0)
        return "%dms" % int(v)
    if kind == 'hz':
        if v >= 1000:
            return "%.1fk" % (v / 1000.0)
        return "%dHz" % int(v)
    if kind == 'ct':
        return "%dc" % int(v)
    return "%.2f" % v




def row_hi(row):
    """A row's upper bound, resolved at read time.

    Only the wavetable rows need this: the catalogue size is not known until
    the SD card has been scanned, and it changes on a rescan."""
    label, key, lo, hi, step, kind, group = row
    if kind == 'wt':
        return max(0, wt_count() - 1)
    if kind == 'sd':
        return max(0, len(_sd_files) - 1)
    return hi


def bump(row, delta):
    """Move a parameter by `delta` encoder detents, and return its apply group."""
    label, key, lo, hi, step, kind, group = eff_row(row)
    if kind in ('wt', 'sd'):
        hi = row_hi(row)
    v = P[key]
    if kind in ('e', 'i', 'a', 'wt', 'sd'):
        v = int(v) + delta
    elif kind == 'hz':
        # Exponential, so a knob feels right across 30 Hz .. 12 kHz.
        v = float(v) * (1.06 ** delta)
        if v < lo:
            v = lo
    elif kind == 'ms' and lo <= 0.0:
        # A 0 ms attack has to stay reachable, so these step linearly at the
        # bottom and exponentially once they are off zero.
        v = float(v) + step * delta if v < 100.0 else float(v) * (1.06 ** delta)
    elif kind == 'ms':
        v = float(v) * (1.06 ** delta)
        if v < lo:
            v = lo
    else:
        v = float(v) + step * delta
    P[key] = clamp(v, lo, hi)

    # ---- rows that are windows onto something else -----------------------
    if key in ("mx_slot", "mx_dest"):
        # Moving the matrix cursor reloads AMOUNT from the routing it now
        # points at, so the row always shows the live value.
        P["mx_amt"] = mx_get(int(P["mx_slot"]), DEST_IDS[int(P["mx_dest"])])
        return 'none'
    if key == "mx_amt":
        slot, dest = int(P["mx_slot"]), DEST_IDS[int(P["mx_dest"])]
        if not mod_can_reach(slot, dest):
            # Not a reachable pair -- see MOD_SLOT_SCOPES.  Refuse rather than
            # store a number that could never do anything.
            P["mx_amt"] = 0.0
            toast("NOT ROUTABLE")
            return 'none'
        mx_set(slot, dest, P["mx_amt"])
        return 'mx'
    if key in ("a_wt", "b_wt"):
        wt_remember_selection()
    return group


def fire_action(key):
    """Momentary rows ('a'): the click IS the value."""
    if key == "panic":
        P["panic"] = 0
        panic()
        toast("PANIC")
    elif key == "mx_clr":
        mx_set(int(P["mx_slot"]), DEST_IDS[int(P["mx_dest"])], 0.0)
        P["mx_amt"] = 0.0
        apply_matrix()
        toast("ROUTE CLEARED")
    elif key == "mx_clrall":
        MATRIX.clear()
        P["fenv"] = 0.0
        P["mx_amt"] = 0.0
        apply_matrix()
        toast("MATRIX CLEARED")
    elif key == "wt_scan_act":
        n = wt_scan_sd()
        P["wt_browse"] = 0
        toast("%d ON SD" % n if n else "NO SD FILES")
    elif key == "wt_load":
        _wt_load_selected()
    P[key] = 0


def _wt_load_selected():
    """Commit the browsed SD file to the chosen oscillator.

    Verifies the table actually loads BEFORE committing the selection, so a
    short or corrupt file reports here rather than going silent on the next
    note.  A file that fails is dropped straight back out of the catalogue, so
    the TABLE knob is never left pointing at a dud."""
    if not _sd_files:
        toast("SCAN SD FIRST")
        return
    rel, path = _sd_files[int(clamp(P["wt_browse"], 0, len(_sd_files) - 1))]
    name = _sd_basename(rel)
    existed = wt_index_of_path(path) >= 0
    idx = wt_add_path(path, name)
    if wt_preset_for(idx) is None:
        if not existed:
            WT_CATALOG.pop()            # remove the fresh, failed append
        # Show the actual reason (bad format, too short, ...) not a bare fail.
        toast((_wt_last_error or "load failed")[:16])
        return
    tgt = int(P["wt_src"])
    P["a_wt" if tgt == 0 else "b_wt"] = idx
    wt_remember_selection()
    (apply_osc_a if tgt == 0 else apply_osc_b)()
    toast("%s>OSC %s" % (name[:7], "A" if tgt == 0 else "B"))


# --------------------------------------------------------------------------
#  SECTION 11 : PATCH MANAGEMENT
# --------------------------------------------------------------------------
#  A patch stores the P dict, the modulation matrix, and the two wavetables BY
#  FILENAME -- never by catalogue index and never as embedded waveform data, as
#  the brief requires.  That means a patch keeps working when the card gains or
#  loses tables, and a missing table is reported rather than silently becoming
#  whatever now sits at the old index.
PATCH_FILE = "/user/wt_patches.json"
PATCH_NAME_MAX = 12
MAX_PATCHES = 24

# Momentary actions and the matrix cursor are UI state, not sound: saving them
# would fire a PANIC (or move somebody's cursor) on every load of that patch.
PATCH_SKIP = ("panic", "mx_clr", "mx_clrall", "mx_slot", "mx_dest", "mx_amt",
              "wt_src", "wt_browse", "wt_load", "wt_scan_act",
              # CV calibration is rig-specific, not part of a sound.
              "cvoff", "cvatt", "cvgate", "cvnote")

DEFAULTS = dict(P)
DEFAULT_MATRIX = dict(MATRIX)


def _capture_patch():
    d = {}
    for k in P:
        if k not in PATCH_SKIP:
            d[k] = P[k]
    # The matrix is keyed by a (slot, dest) tuple, which JSON cannot represent,
    # so it is flattened to "slot:dest" strings on the way out.
    mx = {}
    for (slot, dest), amt in MATRIX.items():
        mx["%d:%s" % (slot, dest)] = amt
    return {"p": d, "mx": mx,
            "a_wt_path": _a_wt_path, "b_wt_path": _b_wt_path}


def _apply_patch(rec):
    """Load a patch snapshot into P/MATRIX and push it to AMY.

    Every key is set, taking the saved value where there is one and the DEFAULT
    where there is not.  Iterating only the saved keys would leave anything the
    snapshot predates at whatever the last patch set it to -- load a heavily
    driven patch, then one saved before DRIVE existed, and the drive comes
    along with it.  That bug is why this loops over DEFAULTS."""
    global _a_wt_path, _b_wt_path
    if not isinstance(rec, dict):
        return False
    d = rec.get("p", {})
    if not isinstance(d, dict):
        return False
    all_off()
    for k in DEFAULTS:
        if k in PATCH_SKIP:
            continue
        P[k] = d[k] if k in d else DEFAULTS[k]
    P["panic"] = 0

    MATRIX.clear()
    mx = rec.get("mx", {})
    if isinstance(mx, dict):
        for k, amt in mx.items():
            try:
                slot_s, dest = k.split(":", 1)
                slot = int(slot_s)
            except Exception:
                continue
            if dest in DEST_IDS and 0 <= slot < NMOD and mod_can_reach(slot, dest):
                MATRIX[(slot, dest)] = amt

    # Wavetables come back by PATH (an absolute path on the card).  Because
    # boot no longer scans, a patch's SD table usually is NOT in the catalogue
    # yet -- so resolve it directly: if the file is still on the card it rejoins
    # the catalogue, a genuinely missing one falls back to the first built-in
    # and says so, rather than loading a different table in silence.
    _a_wt_path = rec.get("a_wt_path")
    _b_wt_path = rec.get("b_wt_path")
    missing = False
    for path, key in ((_a_wt_path, "a_wt"), (_b_wt_path, "b_wt")):
        if path is None:
            continue
        i = wt_index_of_path(path)
        if i < 0 and _file_exists(path):
            i = wt_add_path(path, _sd_basename(path))
        if i >= 0:
            P[key] = i
        else:
            P[key] = 0
            missing = True
    if missing:
        toast("WT MISSING")

    # A patch can change PH.SYNC and the per-osc start phases, neither of which
    # can be un-set without fresh oscillators, so a load always takes the
    # reallocating path.  It has already cut the notes above.
    build_all(full=True)
    apply_fx()
    apply_sys()
    setup_cv()          # a full rebuild resets the oscillators; re-arm the gate
    P["mx_amt"] = mx_get(int(P["mx_slot"]), DEST_IDS[int(P["mx_dest"])])
    return True


def _read_patches():
    # The open() is kept separate from the parse: it is the only thing that
    # tells "no file yet" apart from "file present but corrupt", and a
    # transient read failure must not look like an empty library -- the next
    # save would write that emptiness over a real one.
    try:
        f = open(PATCH_FILE)
    except Exception:
        return []
    try:
        d = json.load(f)
    except Exception as e:
        print("patches unreadable, leaving file alone:", e)
        return []
    finally:
        f.close()
    if isinstance(d, list):
        return [q for q in d if isinstance(q, dict)
                and isinstance(q.get("name"), str)
                and isinstance(q.get("rec"), dict)]
    return []


_patches = _read_patches()
_cur_patch = ""


def _write_patches():
    try:
        with open(PATCH_FILE, "w") as f:
            json.dump(_patches, f)
        return True
    except Exception as e:
        print("patch write failed:", e)
        return False


def _find_patch(name):
    for i in range(len(_patches)):
        if _patches[i].get("name") == name:
            return i
    return -1


def save_patch(name):
    global _cur_patch
    name = name.strip()
    if not name:
        return False
    wt_remember_selection()
    i = _find_patch(name)
    if i >= 0:
        _patches[i]["rec"] = _capture_patch()
    else:
        if len(_patches) >= MAX_PATCHES:
            return False
        _patches.append({"name": name, "rec": _capture_patch()})
    _cur_patch = name
    return _write_patches()


def load_patch(name):
    global _cur_patch
    i = _find_patch(name)
    if i < 0:
        return False
    if not _apply_patch(_patches[i]["rec"]):
        return False
    _cur_patch = name
    return True


def delete_patch(name):
    global _cur_patch
    i = _find_patch(name)
    if i < 0:
        return False
    del _patches[i]
    if _cur_patch == name:
        _cur_patch = ""
    return _write_patches()


def rename_patch(old, new):
    global _cur_patch
    new = new.strip()
    i = _find_patch(old)
    if i < 0 or not new:
        return False
    if _find_patch(new) >= 0 and new != old:
        return False
    _patches[i]["name"] = new
    if _cur_patch == old:
        _cur_patch = new
    return _write_patches()


# --------------------------------------------------------------------------
#  SECTION 12 : OLED / UI LAYER
# --------------------------------------------------------------------------
#  The grid, the colour discipline and the panel workaround are all carried
#  over from the Megatron build, where they were verified on this hardware.
#
#  COLOURS ARE 0..15, NOT 0..255.  amyboard's Display forwards `col` straight
#  through to framebuf: SSD1327 is GS4_HMSB (4 bits, masked to the low nibble)
#  and SH1107 is MONO_VLSB (any non-zero is white).  Writing 0..255 scrambles
#  the SSD1327 -- 200 & 15 == 8.  Where a distinction must survive the 1-bit
#  panel it is carried by SHAPE, not brightness.
C_BRIGHT   = 15
C_VIS      = 14
C_BAR_FILL = 13
C_LABEL    = 7
C_BAR_OUT  = 6
C_TICK     = 5
C_DIM      = 4
C_PAGE_OFF = 1

SCREEN_W = 128
SCREEN_H = 128
CHAR_W = 8
CHAR_H = 8

CAT_Y      = 1
RULE1_Y    = 11
FOCUS_Y    = 15
VIS_Y0     = 24
GRID_BOTTOM = 116
STATUS_Y   = 107
DOTS_Y     = 118
GRID_COLS  = 4
CELL_W     = SCREEN_W // GRID_COLS
# Dropping the per-cell value line lets a cell be just label + bar, freeing
# vertical space: shorter cells push the grid down and give every visual pane
# (waterfall, scope, curves) a taller band -- a cleaner, less cramped layout.
CELL_H     = 22
BAR_W      = 26
BAR_H      = 6
TOAST_MS   = 1400

#  OLED: SH1107 at 0x3D.  amyboard.init_display()'s autodetect binds the wrong
#  driver here -- ssd1327_oled() is pinned to 0x3d and sh1107_oled() to 0x3c,
#  Display() tries the SSD1327 first, and an SH1107 living at 0x3D ACKs that
#  probe.  Nothing raises; it paints noise.  The fix is a TEMPORARY monkeypatch
#  of amyboard's own constructors, then calling amyboard.init_display() as
#  normal -- going through it is what wires up Display.__init__'s background
#  I2C queue, which exists because AMY's audio thread polls the CV ADC on the
#  same bus every audio block.  A hand-built driver would race it and garble.
OLED_ADDR = 0x3D
DISPLAY_ROTATION = 0
DISPLAY_OK = False

PATCH_PAGE = len(PAGES)
N_PAGES = len(PAGES) + 1

page = 0
cursor = 0
editing = False
need_redraw = True
page_mode = False
_toast = ""
_toast_t = 0
enc = None
n_enc = 0
enc_last = [0] * 8
btn_last = False
btn_t = 0


def _now():
    return time.ticks_ms() if hasattr(time, "ticks_ms") else int(time.time() * 1000)


def _dt(a, b):
    return time.ticks_diff(a, b) if hasattr(time, "ticks_diff") else (a - b)


def toast(msg):
    global _toast, _toast_t, need_redraw
    _toast = msg
    _toast_t = _now()
    need_redraw = True


def need_ui():
    global need_redraw
    need_redraw = True


def init_display():
    global DISPLAY_OK
    orig_sh = getattr(amyboard, "sh1107_oled", None)
    orig_ssd = getattr(amyboard, "ssd1327_oled", None)
    try:
        def _sh1107_forced(rotate=0):
            import sh1107
            d = sh1107.SH1107_I2C(128, 128, amyboard.get_i2c(),
                                  address=OLED_ADDR, rotate=DISPLAY_ROTATION)
            d.sleep(False)
            return d

        def _ssd1327_disabled():
            # Must RAISE, not return None: Display() keeps the first
            # constructor that does not raise, so this is how the SSD1327
            # branch is skipped and the SH1107 one reached.
            raise OSError("ssd1327 disabled: panel is SH1107 at 0x%02X" % OLED_ADDR)

        amyboard.sh1107_oled = _sh1107_forced
        amyboard.ssd1327_oled = _ssd1327_disabled
        amyboard.init_display()
    except Exception as e:
        print("init_display: failed (%s) -- retrying with autodetect" % e)
        try:
            amyboard.init_display()
        except Exception as e2:
            print("init_display: autodetect also failed:", e2)
    finally:
        if orig_sh is not None:
            amyboard.sh1107_oled = orig_sh
        if orig_ssd is not None:
            amyboard.ssd1327_oled = orig_ssd
    try:
        DISPLAY_OK = amyboard.display is not None and amyboard.display.available
    except Exception:
        DISPLAY_OK = False
    print("init_display: SH1107 at 0x%02X rot %d -- %s"
          % (OLED_ADDR, DISPLAY_ROTATION, "OK" if DISPLAY_OK else "no panel"))
    return DISPLAY_OK


def display_refresh():
    if DISPLAY_OK:
        try:
            amyboard.display_refresh()
        except Exception as e:
            print("display_refresh failed:", e)


def is_patch_page():
    return page == PATCH_PAGE


def cur_rows():
    if is_patch_page():
        return []
    return PAGES[page][1]


def cell_norm(row):
    """(fill 0..1, bipolar) for a row's bar."""
    label, key, lo, hi, step, kind, group = eff_row(row)
    if kind in ('wt', 'sd'):
        hi = row_hi(row)
    v = float(P[key])
    if hi <= lo:
        return 0.0, False
    if kind in ('hz', 'ms') and lo > 0.0 and (hi / lo) > 20.0:
        # Log fill, matching the exponential stepping these knobs use: on a
        # linear bar a 30 Hz .. 12 kHz cutoff sits pinned at the far left for
        # the whole musically useful part of its travel.
        v = clamp(v, lo, hi)
        return clamp((math.log(v) - math.log(lo))
                     / (math.log(hi) - math.log(lo)), 0.0, 1.0), False
    return clamp((v - lo) / (hi - lo), 0.0, 1.0), lo < 0.0


def grid_y0(n_params):
    n_rows = (max(1, n_params) + GRID_COLS - 1) // GRID_COLS
    return GRID_BOTTOM - n_rows * CELL_H


def cell_xy(i, n_params):
    y0 = grid_y0(n_params)
    return (i % GRID_COLS) * CELL_W, y0 + (i // GRID_COLS) * CELL_H


def vis_band():
    """(top_y, height) of the visual pane on the CURRENT page -- derived from
    the grid, so a page with fewer rows automatically gets a taller picture."""
    n = len(cur_rows())
    return VIS_Y0, grid_y0(n) - VIS_Y0 - 2


def draw_dots(d, y, cur, total):
    w, h, off_w = 5, 2, 2
    # Tighten the gap before giving up: 15 screens do not fit at a 4px pitch.
    gap = 4
    while gap > 1 and total * w + (total - 1) * gap > SCREEN_W:
        gap -= 1
    span = total * w + (total - 1) * gap
    x = (SCREEN_W - span) // 2
    if x < 0:
        # More screens than fit at full pitch: fall back to a plain readout.
        d.text("%d/%d" % (cur + 1, total), 2, y - 3, C_DIM)
        return
    for i in range(total):
        if i == cur:
            d.fill_rect(x, y, w, h, C_BRIGHT)
        else:
            d.fill_rect(x + (w - off_w) // 2, y, off_w, h, C_PAGE_OFF)
        x += w + gap


def draw_cell(d, x0, y0, label, n01, bip, state):
    """One grid cell: a 3-letter label and its bar -- no number.

    The live value is shown in full at the top of the page for the focused
    parameter, so repeating it in every cell was just clutter.  state: 0 = idle,
    1 = cursor, 2 = selected (being edited)."""
    cx = x0 + CELL_W // 2
    if state == 2:
        d.fill_rect(x0, y0, CELL_W, CELL_H - 2, C_BRIGHT)
        fg = bout = bfill = tick = 0
    else:
        fg, bout, bfill, tick = C_LABEL, C_BAR_OUT, C_BAR_FILL, C_TICK
        if state == 1:
            fg = bout = bfill = tick = C_BRIGHT
            d.fill_rect(x0, y0 + CELL_H - 2, CELL_W, 1, C_BRIGHT)
    lx = cx - (len(label) * CHAR_W) // 2
    d.text(label, max(x0, lx), y0 + 3, fg)
    bx = cx - BAR_W // 2
    by = y0 + 13
    d.fill_rect(bx, by, BAR_W, 1, bout)
    d.fill_rect(bx, by + BAR_H - 1, BAR_W, 1, bout)
    d.fill_rect(bx, by, 1, BAR_H, bout)
    d.fill_rect(bx + BAR_W - 1, by, 1, BAR_H, bout)
    if bip:
        cb = bx + BAR_W // 2
        d.fill_rect(cb, by, 1, BAR_H, tick)
        half = (BAR_W - 4) // 2
        w = int(round(half * (n01 - 0.5) * 2))
        if w > 0:
            d.fill_rect(cb, by + 2, w, BAR_H - 4, bfill)
        elif w < 0:
            d.fill_rect(cb + w, by + 2, -w, BAR_H - 4, bfill)
    else:
        fw = int(round((BAR_W - 4) * n01))
        if fw > 0:
            d.fill_rect(bx + 2, by + 2, fw, BAR_H - 4, bfill)


# --------------------------------------------------------------------------
#  VISUAL PANE
# --------------------------------------------------------------------------
#  Every page gets a picture of what its settings are doing.  Each one is
#  self-contained (clears its own band, draws nothing else) and driven straight
#  off P[...], redrawn only on the need_redraw path -- a knob turn or a cursor
#  move -- so they cost nothing while you are just playing.  The MIX-page
#  oscilloscope is the one exception: audio moves without any user input, so it
#  gets its own throttled refresh from loop().
SCOPE_NCHANS = 2                # AMY_NCHANS is 2 here; the buffer is interleaved
_scope_fault = False

# Stable pseudo-random offsets, -1..1.  A fixed TABLE rather than a live
# random(), so a "scattered" picture holds still while a knob moves instead of
# shimmering and reading as noise.
VJIT = (0.31, -0.72, 0.55, -0.18, 0.88, -0.45, 0.12, -0.63)


def _vrect(d, x, y, w, h, col, y_lo, y_hi):
    x, y, w, h = int(x), int(y), int(w), int(h)
    if y < y_lo:
        h -= (y_lo - y)
        y = y_lo
    if y + h > y_hi:
        h = y_hi - y
    if h <= 0 or w <= 0 or x >= SCREEN_W:
        return
    if x < 0:
        w += x
        x = 0
    if x + w > SCREEN_W:
        w = SCREEN_W - x
    if w > 0:
        d.fill_rect(x, y, w, h, col)


def _vtrace(d, pts, col, y_lo, y_hi):
    i = 1
    while i < len(pts):
        x0, y0 = pts[i - 1]
        x1, y1 = pts[i]
        y0 = clamp(y0, y_lo, y_hi - 1)
        y1 = clamp(y1, y_lo, y_hi - 1)
        d.line(int(x0), int(y0), int(x1), int(y1), col)
        i += 1


def _vtrace_dither(d, pts, col, y_lo, y_hi):
    """Draw a polyline as a 50%% checkerboard of pixels.

    On the 1-bit SH1107 (pixels are on or off) this is how you get a DIM grey:
    lighting every other pixel in a fixed (x+y) parity reads as a uniform grey
    wash to the eye, distinct from a solid (full-brightness) line -- exactly the
    grey terrain / bright highlight look, with no thick line and no per-frame
    flicker.  On a greyscale panel `col` (C_DIM) makes it grey natively; the
    dither only makes it a touch dimmer, which is fine."""
    i = 1
    while i < len(pts):
        x0, y0 = int(pts[i - 1][0]), int(clamp(pts[i - 1][1], y_lo, y_hi - 1))
        x1, y1 = int(pts[i][0]), int(clamp(pts[i][1], y_lo, y_hi - 1))
        dx = x1 - x0 if x1 >= x0 else x0 - x1
        dy = -(y1 - y0) if y1 >= y0 else -(y0 - y1)
        sx = 1 if x0 < x1 else -1
        sy = 1 if y0 < y1 else -1
        err = dx + dy
        while True:
            if ((x0 + y0) & 1) == 0:            # 50%% dither -> perceived grey
                d.pixel(x0, y0, col)
            if x0 == x1 and y0 == y1:
                break
            e2 = 2 * err
            if e2 >= dy:
                err += dy
                x0 += sx
            if e2 <= dx:
                err += dx
                y0 += sy
        i += 1


def draw_scope(d):
    """Live post-FX output waveform, read straight off AMY's last-rendered
    block (amy.get_output_buffer() -- src/api.c returns the exact bytes about
    to reach the DAC, bus FX included, not a synthetic preview).

    Touches only its own band: no d.fill(0), no full-screen redraw."""
    global _scope_fault
    y_top, h = vis_band()
    d.fill_rect(0, y_top, SCREEN_W, h, 0)
    try:
        buf = amy.get_output_buffer()
    except Exception as e:
        if not _scope_fault:
            _scope_fault = True
            print("scope: amy.get_output_buffer() failed:", e)
        buf = None
    if not buf:
        return
    try:
        samples = array.array('h', buf)
    except Exception as e:
        if not _scope_fault:
            _scope_fault = True
            print("scope: buffer decode failed:", e)
        return
    n = len(samples) // SCOPE_NCHANS
    if n < 2:
        return
    mid = y_top + h // 2
    half = h // 2 - 1
    prev_y = mid
    x = 0
    step = max(1, n // SCREEN_W)
    while x < SCREEN_W and x * step < n:
        s = samples[(x * step) * SCOPE_NCHANS]      # left channel
        y = clamp(mid - (s * half) // 32768, y_top, y_top + h - 1)
        if x == 0:
            d.pixel(x, y, C_VIS)
        else:
            d.line(x - 1, prev_y, x, y, C_VIS)
        prev_y = y
        x += 1


def _adsr_widths(a_ms, d_ms, r_ms):
    # Log-compressed, so a 5 ms attack next to an 8 s release each still get a
    # visible sliver instead of one collapsing to nothing.
    la = math.log(max(a_ms, 1.0) + 1.0)
    ld = math.log(max(d_ms, 1.0) + 1.0)
    lr = math.log(max(r_ms, 1.0) + 1.0)
    total = la + ld + lr
    if total <= 0.0:
        total = 1.0
    return la / total, ld / total, lr / total


def draw_adsr(d, a_ms, d_ms, s_lvl, r_ms):
    """Attack always rises to FULL peak -- matching AMY, where sustain is the
    level decay falls TO, not the attack's target."""
    y_top, h = vis_band()
    d.fill_rect(0, y_top, SCREEN_W, h, 0)
    x0, x1 = 2, SCREEN_W - 2
    bot, top = y_top + h - 1, y_top
    fa, fd, fr = _adsr_widths(a_ms, d_ms, r_ms)
    w = x1 - x0
    hold_w = max(4, int(w * 0.14))
    remain = max(0, w - hold_w)
    aw = max(3, int(remain * fa))
    dw = max(3, int(remain * fd))
    rw = max(3, remain - aw - dw)
    sy = bot - int(round((bot - top) * clamp(s_lvl, 0.0, 1.0)))
    xa = x0 + aw
    xdc = xa + dw
    xs = xdc + hold_w
    d.line(x0, bot, xa, top, C_VIS)
    d.line(xa, top, xdc, sy, C_VIS)
    d.line(xdc, sy, xs, sy, C_VIS)
    d.line(xs, sy, min(xs + rw, x1), bot, C_VIS)


def draw_vis_wavetable(d, y0, h, which):
    """Topographic waterfall of the ACTUAL wavetable, Ableton-style.

    Every frame of the table is drawn as a stacked waveform line, receding with
    a slight parallax skew.  The terrain is drawn DIM -- a 50%% checkerboard
    dither, which the 1-bit SH1107 shows as grey -- and the frame at the current
    POSITION is drawn SOLID (full brightness), so the highlight reads by
    brightness rather than by thickness.  On a greyscale panel the same
    C_DIM/C_BRIGHT colours give the grey/white directly.  The data is the real
    table -- from the generator for a built-in, from the loaded samples for an
    SD table -- so the picture and the sound never disagree."""
    y_hi = y0 + h
    d.fill_rect(0, y0, SCREEN_W, h, 0)
    pos = clamp(P[which + "_pos"], 0.0, 1.0)
    lines = _wt_preview_for(int(P[which + "_wt"]))
    if not lines:
        # ROM fallback (no sample data in Python): just a position bar.
        _vrect(d, 2, y_hi - 4, int((SCREEN_W - 4) * pos), 2, C_BRIGHT, y0, y_hi)
        return

    n = len(lines)
    npts = len(lines[0])
    cur = int(pos * (n - 1) + 0.5)
    if cur < 0:
        cur = 0
    elif cur > n - 1:
        cur = n - 1
    # Geometry tuned to whatever band height this page has (OSC A/B leave ~32px).
    skew = 10 if h >= 20 else 4                 # total horizontal parallax
    dx = skew / float(n)
    top = y0 + 1
    avail = h - 2
    spacing = avail / float(n)                  # vertical step between frames
    amp = spacing * 1.7                          # waveforms overlap -> "terrain"
    xspan = SCREEN_W - skew - 2

    def frame_pts(li):
        yb = top + int(li * spacing) + int(amp * 0.5)
        xo = 1 + int((n - 1 - li) * dx)          # top frames pushed right
        pts = []
        row = lines[li]
        for i in range(npts):
            x = xo + int(i * (xspan - 1) / float(npts - 1))
            yy = yb - int(row[i] * amp * 0.5)
            pts.append((x, yy))
        return pts

    # DIM terrain (dithered grey), back-to-front so nearer lines overdraw
    # farther ones.  A one-pixel black skirt just below the selected frame
    # clears the dither immediately under it, so the solid highlight sits on a
    # clean edge rather than blending into the checkerboard.
    sel = frame_pts(cur)
    for li in range(n):
        if li == cur:
            continue
        _vtrace_dither(d, frame_pts(li), C_DIM, y0, y_hi)
    for (x, yy) in sel:
        if y0 <= yy + 1 < y_hi:
            d.pixel(x, yy + 1, 0)

    # BRIGHT highlight: a single solid line at full brightness -- distinct from
    # the 50%% terrain by luminance, not by thickness.  No numeric readout: the
    # waterfall already shows where POSITION sits, and its value is on the
    # header when the row is focused.
    _vtrace(d, sel, C_BRIGHT, y0, y_hi)


def draw_vis_filter(d, y0, h):
    """Filter response.  x is log frequency over 20 Hz .. 20 kHz, so CUTOFF's
    screen position matches the log-scaled CUT bar in the grid below.  A shape
    that tracks the knobs, drawn cheaply -- not a measured plot."""
    y_hi = y0 + h
    d.fill_rect(0, y0, SCREEN_W, h, 0)
    ftype = int(P["ftype"])
    lo_l = math.log(20.0)
    span_l = math.log(20000.0) - lo_l
    oct_per_px = (span_l / math.log(2.0)) / float(SCREEN_W)
    xc = (math.log(clamp(P["cutoff"], 20.0, 20000.0)) - lo_l) / span_l * SCREEN_W
    reso_db = clamp((P["reso"] - 0.5) / 15.5, 0.0, 1.0) * 22.0
    top_db, bot_db = 24.0, -48.0
    pts = []
    x = 0
    while x < SCREEN_W:
        dd = (x - xc) * oct_per_px
        a = dd if dd >= 0 else -dd
        if ftype == 0:
            g = 0.0
        elif ftype == 1:
            g = 0.0 if dd < 0 else -12.0 * dd
        elif ftype == 4:
            g = 0.0 if dd < 0 else -24.0 * dd
        elif ftype == 3:
            g = 0.0 if dd > 0 else -12.0 * a
        elif ftype == 2:
            g = -9.0 * a
        elif ftype == 5:
            g = -34.0 / (1.0 + (a * 3.2) ** 2)
        else:
            g = -7.0 / (1.0 + (a * 2.2) ** 2) + 5.0 * math.sin(dd * 2.4)
        if ftype not in (0, 5):
            g += reso_db / (1.0 + (dd * 3.0) ** 2)
        g = clamp(g, bot_db, top_db)
        pts.append((x, y0 + (top_db - g) / (top_db - bot_db) * (h - 1)))
        x += 2
    _vtrace(d, pts, C_VIS, y0, y_hi)


def draw_vis_lfo(d, y0, h, n):
    """The modulator's own waveform.

    In AUDIO mode it is drawn dense and labelled FM/RM, because at that rate it
    is an operator rather than an LFO and the distinction is the whole point of
    the MODE row."""
    y_hi = y0 + h
    d.fill_rect(0, y0, SCREEN_W, h, 0)
    shape = int(clamp(P["m%d_shape" % n], 0, len(LFO_SHAPES) - 1))
    depth = clamp(P["m%d_depth" % n], 0.0, 1.0)
    audio = P["m%d_mode" % n] == 1
    cycles = 6.0 if audio else clamp(mod_rate_hz(n) * 1.5, 0.5, 6.0)
    ph0 = clamp(P["m%d_phase" % n], 0.0, 1.0)
    mid = y0 + h // 2
    amp = (h // 2 - 2) * depth
    pts = []
    for x in range(0, SCREEN_W, 2):
        t = (x / float(SCREEN_W)) * cycles + ph0
        f = t - int(t)
        if shape == 0:
            v = math.sin(2 * math.pi * t)
        elif shape == 1:
            v = 4.0 * abs(f - 0.5) - 1.0
        elif shape == 2:
            v = 1.0 - 2.0 * f
        elif shape == 3:
            v = 2.0 * f - 1.0
        elif shape == 4:
            v = 1.0 if f < 0.5 else -1.0
        else:
            v = VJIT[int(t) % len(VJIT)]
        pts.append((x, mid - v * amp))
    _vtrace(d, pts, C_VIS, y0, y_hi)
    if audio:
        d.text("FM/RM", SCREEN_W - 5 * CHAR_W - 1, y0, C_DIM)


def draw_vis_matrix(d, y0, h):
    """The whole 4 x 11 matrix at a glance.

    Rows are the four modulators, columns the destinations.  A filled block is
    a live routing (its height is the amount), a single dim pixel is a
    reachable-but-unused pair, and a blank column for that row is a pair the
    modulator physically cannot reach -- see MOD_SLOT_SCOPES.  The cursor cell
    is bracketed."""
    y_hi = y0 + h
    d.fill_rect(0, y0, SCREEN_W, h, 0)
    nd = len(DESTS)
    cw = SCREEN_W // nd
    rh = max(3, (h - 2) // NMOD)
    cs, cd = int(P["mx_slot"]), int(P["mx_dest"])
    for slot in range(NMOD):
        ry = y0 + slot * rh
        for di in range(nd):
            dest = DEST_IDS[di]
            x = di * cw
            if not mod_can_reach(slot, dest):
                continue
            amt = mx_get(slot, dest)
            if amt == 0.0:
                d.pixel(x + cw // 2, ry + rh // 2, C_PAGE_OFF)
            else:
                mag = clamp(abs(amt) / 4.0, 0.12, 1.0)
                bh = max(1, int((rh - 1) * mag))
                _vrect(d, x + 1, ry + (rh - 1 - bh), max(1, cw - 2), bh,
                       C_VIS, y0, y_hi)
        if slot == cs:
            _vrect(d, cd * cw, ry, 1, rh, C_BRIGHT, y0, y_hi)
            _vrect(d, cd * cw + cw - 1, ry, 1, rh, C_BRIGHT, y0, y_hi)


def draw_vis_unison(d, y0, h):
    """Four voices, spread by DETUNE horizontally and WIDTH into the stereo
    field -- exactly the two knobs on the page."""
    y_hi = y0 + h
    d.fill_rect(0, y0, SCREEN_W, h, 0)
    sq = 7
    for v in range(NVOICE):
        cents = UNI_DETUNE[v] * P["uni_det"]
        x = SCREEN_W / 2.0 + (cents / 50.0) * (SCREEN_W / 2.0 - sq)
        pan = clamp(0.5 + UNI_PAN[v] * P["uni_width"] * 0.5, 0.0, 1.0)
        y = y0 + 2 + (h - sq - 4) * pan
        _vrect(d, x - sq / 2, y, sq, sq, C_VIS, y0, y_hi)
    _vrect(d, SCREEN_W // 2, y0, 1, h, C_PAGE_OFF, y0, y_hi)


def draw_vis_wtload(d, y0, h):
    """The SD browser: the file list with the cursor, and the load target.

    Empty until SCAN SD is run, which is the whole point -- the card is only
    read on demand."""
    y_hi = y0 + h
    d.fill_rect(0, y0, SCREEN_W, h, 0)
    tgt = "A" if int(P["wt_src"]) == 0 else "B"
    d.text("-> OSC %s   %d FILES" % (tgt, len(_sd_files)), 2, y0, C_DIM)
    if not _sd_files:
        d.text("RUN SCAN SD", 2, y0 + 14, C_LABEL)
        d.text("TO LIST .wav", 2, y0 + 26, C_DIM)
        d.text("ON THE CARD", 2, y0 + 38, C_DIM)
        return
    sel = int(clamp(P["wt_browse"], 0, len(_sd_files) - 1))
    top = max(0, min(sel - 2, max(0, len(_sd_files) - 5)))
    for k in range(5):
        i = top + k
        if i >= len(_sd_files):
            break
        y = y0 + 12 + k * 10
        if y + 8 > y_hi:
            break
        name = _sd_basename(_sd_files[i][0])
        if i == sel:
            _vrect(d, 0, y - 1, SCREEN_W, 9, C_VIS, y0, y_hi)
            d.text(name[:15], 2, y, 0)
        else:
            d.text(name[:15], 2, y, C_LABEL)


def draw_vis_voices(d, y0, h):
    """Which voices are sounding, and the mode that put them there."""
    y_hi = y0 + h
    d.fill_rect(0, y0, SCREEN_W, h, 0)
    d.text(VOICE_MODES[int(P["vmode"])], 2, y0, C_DIM)
    bw = SCREEN_W // NVOICE
    for v in range(NVOICE):
        x = v * bw + 4
        y = y0 + 12
        bh = max(4, h - 16)
        if _vnote[v] is None:
            _vrect(d, x, y + bh - 2, bw - 8, 2, C_PAGE_OFF, y0, y_hi)
        else:
            _vrect(d, x, y, bw - 8, bh, C_VIS, y0, y_hi)
            d.text(str(int(_vnote[v])), x, y + bh // 2 - 4, 0)


def draw_vis_drive(d, y0, h):
    """The distortion transfer curve, clip and fold stages included."""
    y_hi = y0 + h
    d.fill_rect(0, y0, SCREEN_W, h, 0)
    drive = clamp(P["d_drive"], 0.0625, 16.0)
    pts = []
    for x in range(0, SCREEN_W, 2):
        v = (x / float(SCREEN_W)) * 2.0 - 1.0
        y = v * drive
        if P["d_fold"]:
            for _ in range(4):
                if y > 1.0:
                    y = 2.0 - y
                elif y < -1.0:
                    y = -2.0 - y
        if P["d_clip"] or not P["d_fold"]:
            y = y - (y * y * y) / 3.0 if abs(y) < 1.0 else (1.0 if y > 0 else -1.0)
        y = clamp(y * clamp(P["d_mix"], 0.0, 1.0), -1.0, 1.0)
        pts.append((x, y0 + h / 2.0 - y * (h / 2.0 - 1)))
    _vtrace(d, pts, C_VIS, y0, y_hi)


def _bars(d, y0, h, items):
    """A labelled bar per (name, 0..1) pair -- used by the two FX pages.

    The track is an OUTLINE, not a filled rectangle.  On the 1-bit SH1107 any
    non-zero colour is white, so a solid track (even at the dimmest level) reads
    as a FULL white bar -- which is exactly the "bars look full by default" bug.
    An outline reads as an empty bar that fills from the left with white as the
    value rises, matching the grid cells below."""
    y_hi = y0 + h
    d.fill_rect(0, y0, SCREEN_W, h, 0)
    n = len(items)
    if n == 0:
        return
    rh = max(6, h // n)
    bx = 5 * CHAR_W
    bw = SCREEN_W - bx - 3
    for i in range(n):
        name, v = items[i]
        y = y0 + i * rh
        bh = rh - 3
        d.text(name[:4], 1, y, C_DIM)
        # Empty outline box (thin lines, so it never reads as "full").
        _vrect(d, bx, y + 1, bw, 1, C_BAR_OUT, y0, y_hi)
        _vrect(d, bx, y + bh, bw, 1, C_BAR_OUT, y0, y_hi)
        _vrect(d, bx, y + 1, 1, bh, C_BAR_OUT, y0, y_hi)
        _vrect(d, bx + bw - 1, y + 1, 1, bh, C_BAR_OUT, y0, y_hi)
        # Fill proportional to the value, inset one pixel inside the outline.
        fw = int((bw - 2) * clamp(v, 0.0, 1.0))
        if fw > 0:
            _vrect(d, bx + 1, y + 2, fw, bh - 2, C_VIS, y0, y_hi)


# ---- CV CAL visual pane (ported from megatron_v1) -------------------------
NOTE_NAMES = ("C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B")
CV_VIS_MS = 250
_cv_vis_t = 0
_cv_vis_last = (None, None)
_cv_vis_fault = False


def _note_name(n):
    """Fractional MIDI note -> e.g. "C4+7" (nearest name, octave, cents off)."""
    if n < 0 or n > 127:
        return "--"
    nearest = int(round(n))
    cents = int(round((n - nearest) * 100.0))
    nm = NOTE_NAMES[nearest % 12] + "%d" % (nearest // 12 - 1)
    if cents:
        nm += "%+d" % cents
    return nm


def _vtext(d, s, x, y, col, y0, y_hi):
    """Text clipped to the panel: an over-wide .text() writes outside the
    framebuffer rather than truncating, so every variable-length readout on
    the visual pane goes through here."""
    if y < y0 or y + 8 > y_hi:
        return
    room = (SCREEN_W - x) // CHAR_W
    if room > 0:
        d.text(s[:room], x, y, col)


def cv_read_both():
    """(gate_v, pitch_v) for the display, throttled.  (None, None) if no cv_in."""
    global _cv_vis_t, _cv_vis_last, _cv_vis_fault
    now = _now()
    if _cv_vis_last[0] is not None and _dt(now, _cv_vis_t) < CV_VIS_MS:
        return _cv_vis_last
    try:
        g = amyboard.cv_in(CV_GATE_INPUT)
        v = amyboard.cv_in(CV_PITCH_INPUT)
    except Exception as e:
        if not _cv_vis_fault:
            _cv_vis_fault = True
            print("CV display: cv_in() unavailable:", e)
        return None, None
    _cv_vis_t = now
    _cv_vis_last = (g, v)
    return g, v


def draw_vis_cvcal(d, y0, h):
    """Live CV, the trigger state, and where the calibration currently stands.

    Both jacks are shown and labelled BY JACK: if you gate CV1 and the CV1 line
    does not move, the problem is which physical jack maps to which AMY
    channel, and no threshold tuning will fix that."""
    y_hi = y0 + h
    _vrect(d, 0, y0, SCREEN_W, h, 0, y0, y_hi)   # this pane redraws live
    gv, pv = cv_read_both()
    if gv is None:
        _vtext(d, "no cv_in()", 2, y0 + h // 2 - 4, C_VIS, y0, y_hi)
        return
    # CV1 gate: RAW volts (AMY thresholds against the raw reading), with the
    # threshold and live trigger state alongside so the margin is visible.
    _vtext(d, "CV1 %+.2f>%.1f %s" % (clamp(gv, -9.9, 9.9), CV_GATE_ON,
                                     "TRIG" if gv >= CV_GATE_ON else "--"),
           2, y0 + 1, C_VIS, y0, y_hi)
    # CV2 pitch: CORRECTED volts (raw + ATTEN + OFFSET), the number the synth
    # actually plays from, plus the note it resolves to.
    corr = pv + cv_offset_volts()
    _vtext(d, "CV2 %+.2fV %s" % (clamp(corr, -9.9, 9.9),
                                 _note_name(cv_note_for(pv))),
           2, y0 + 10, C_VIS, y0, y_hi)
    _vtext(d, "raw %+.2f trim%+.2f" % (clamp(pv, -9.9, 9.9), cv_offset_volts()),
           2, y0 + 19, C_VIS, y0, y_hi)


def draw_visual(d):
    """Dispatch by page NAME, not index -- reordering PAGES cannot then point a
    picture at the wrong screen."""
    name = PAGES[page][0]
    y0, h = vis_band()
    if h < 8:
        return
    if name == "OSC A":
        draw_vis_wavetable(d, y0, h, "a")
    elif name == "OSC B":
        draw_vis_wavetable(d, y0, h, "b")
    elif name == "WT LOAD":
        draw_vis_wtload(d, y0, h)
    elif name == "MIX":
        # The output oscilloscope lives here: MIX is this synth's main page.
        draw_scope(d)
    elif name == "FILTER":
        draw_vis_filter(d, y0, h)
    elif name == "ENV":
        draw_adsr(d, P["aa"], P["ad"], P["as"], P["ar"])
    elif name == "MOD 1":
        draw_vis_lfo(d, y0, h, 1)
    elif name == "MOD 2":
        draw_vis_lfo(d, y0, h, 2)
    elif name == "MOD 3":
        draw_adsr(d, P["m3_a"], P["m3_d"], P["m3_s"], P["m3_r"])
    elif name == "MOD 4":
        draw_adsr(d, P["m4_a"], P["m4_d"], P["m4_s"], P["m4_r"])
    elif name == "MATRIX":
        draw_vis_matrix(d, y0, h)
    elif name == "UNISON":
        draw_vis_unison(d, y0, h)
    elif name == "DRIVE":
        draw_vis_drive(d, y0, h)
    elif name == "FX":
        _bars(d, y0, h, [("CHOR", P["ch_lvl"]), ("ECHO", P["ec_lvl"]),
                         ("FB", P["ec_fb"] / 0.9)])
    elif name == "REVERB":
        _bars(d, y0, h, [("REVB", P["rv_lvl"]), ("LIVE", P["rv_live"]),
                         ("DAMP", P["rv_damp"])])
    elif name == "CV CAL":
        draw_vis_cvcal(d, y0, h)


# --------------------------------------------------------------------------
#  PAGE CHROME
# --------------------------------------------------------------------------

def draw_page_header(d, title, right, right_col):
    """In PAGE MODE the whole bar is knocked out -- an unmistakable "you are
    picking a screen, this is not live yet", reusing the same knockout language
    a selected grid cell already uses."""
    if page_mode:
        d.fill_rect(0, 0, SCREEN_W, RULE1_Y, C_BRIGHT)
        d.text(title[:10], 2, CAT_Y, 0)
        if right:
            d.text(right, SCREEN_W - 2 - CHAR_W * len(right), CAT_Y, 0)
    else:
        d.text(title[:10], 2, CAT_Y, C_BRIGHT)
        if right:
            d.text(right, SCREEN_W - 2 - CHAR_W * len(right), CAT_Y, right_col)
        d.fill_rect(0, RULE1_Y, SCREEN_W, 1, C_DIM)


def draw_grid(d):
    rows = cur_rows()
    draw_page_header(d, PAGES[page][0], _cur_patch[:6] if _cur_patch else "",
                     C_DIM)
    if _toast and _dt(_now(), _toast_t) < TOAST_MS:
        d.text(_toast[:16], 2, FOCUS_Y, C_BRIGHT)
    elif 0 <= cursor < len(rows):
        label, key, lo, hi, step, kind, group = eff_row(rows[cursor])
        d.text(label[:9], 2, FOCUS_Y, C_LABEL)
        v = fmt_value(key, kind, P[key])
        d.text(v, SCREEN_W - 2 - CHAR_W * len(v), FOCUS_Y, C_BRIGHT)
    draw_visual(d)
    for i in range(len(rows)):
        row = eff_row(rows[i])
        label, key, lo, hi, step, kind, group = row
        x0, y0 = cell_xy(i, len(rows))
        n01, bip = cell_norm(rows[i])
        state = 2 if (i == cursor and editing) else (1 if i == cursor else 0)
        draw_cell(d, x0, y0, SHORT.get(key, label[:3]), n01, bip, state)
    draw_dots(d, DOTS_Y, page, N_PAGES)


# --------------------------------------------------------------------------
#  PATCH SCREEN -- a list, not a grid: it is the one screen whose contents
#  change at runtime, and a name has to be typed rather than dialled.
# --------------------------------------------------------------------------
pmode = 'list'          # 'list' | 'menu' | 'name'
plist_i = 0
pmenu_i = 0
_name_buf = ""
_name_i = 0
_rename_of = ""
NAME_CHARS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 -_"
PMENU = ["LOAD", "SAVE OVER", "RENAME", "DELETE"]


def _plist_items():
    """The patch list, with the two always-present actions on top."""
    return ["<NEW PATCH>", "<RESCAN WT>"] + [q["name"] for q in _patches]


def draw_patches(d):
    draw_page_header(d, "PATCH", _cur_patch[:6] if _cur_patch else "", C_DIM)
    if pmode == 'name':
        d.text("NAME:", 2, FOCUS_Y, C_LABEL)
        d.text(_name_buf[:12], 2, FOCUS_Y + 14, C_BRIGHT)
        ch = NAME_CHARS[_name_i % len(NAME_CHARS)]
        d.text("[" + ch + "]", 2, FOCUS_Y + 28, C_BRIGHT)
        d.text("CLICK=ADD", 2, FOCUS_Y + 44, C_DIM)
        d.text("HOLD=DONE", 2, FOCUS_Y + 56, C_DIM)
        draw_dots(d, DOTS_Y, page, N_PAGES)
        return
    if pmode == 'menu':
        d.text(_cur_sel_name()[:14], 2, FOCUS_Y, C_LABEL)
        for i in range(len(PMENU)):
            y = FOCUS_Y + 16 + i * 12
            if i == pmenu_i:
                d.fill_rect(0, y - 1, SCREEN_W, 11, C_BRIGHT)
                d.text(PMENU[i], 4, y, 0)
            else:
                d.text(PMENU[i], 4, y, C_LABEL)
        draw_dots(d, DOTS_Y, page, N_PAGES)
        return
    items = _plist_items()
    if _toast and _dt(_now(), _toast_t) < TOAST_MS:
        d.text(_toast[:16], 2, FOCUS_Y, C_BRIGHT)
    else:
        d.text("%d/%d" % (plist_i + 1, len(items)), 2, FOCUS_Y, C_DIM)
    # A window of six around the cursor, so a long library still scrolls.
    top = max(0, min(plist_i - 2, max(0, len(items) - 6)))
    for k in range(6):
        i = top + k
        if i >= len(items):
            break
        y = VIS_Y0 + 4 + k * 13
        if i == plist_i:
            d.fill_rect(0, y - 1, SCREEN_W, 12, C_BRIGHT)
            d.text(items[i][:15], 3, y, 0)
        else:
            d.text(items[i][:15], 3, y, C_LABEL)
    draw_dots(d, DOTS_Y, page, N_PAGES)


def _cur_sel_name():
    items = _plist_items()
    if 0 <= plist_i < len(items):
        return items[plist_i]
    return ""


def patch_turn(delta):
    global plist_i, pmenu_i, _name_i, need_redraw
    if pmode == 'list':
        n = len(_plist_items())
        plist_i = int(clamp(plist_i + delta, 0, max(0, n - 1)))
    elif pmode == 'menu':
        pmenu_i = int(clamp(pmenu_i + delta, 0, len(PMENU) - 1))
    else:
        _name_i = (_name_i + delta) % len(NAME_CHARS)
    need_redraw = True


def _start_name(initial="", rename_of=""):
    global pmode, _name_buf, _name_i, _rename_of, need_redraw
    pmode = 'name'
    _name_buf = initial
    _name_i = 0
    _rename_of = rename_of
    need_redraw = True


def _commit_name():
    global pmode, need_redraw
    name = _name_buf.strip()
    if not name:
        toast("NAME EMPTY")
    elif _rename_of:
        toast("RENAMED" if rename_patch(_rename_of, name) else "RENAME FAILED")
    else:
        toast("SAVED" if save_patch(name) else "SAVE FAILED")
    pmode = 'list'
    need_redraw = True


def patch_click():
    global pmode, pmenu_i, _name_buf, need_redraw
    if pmode == 'name':
        if len(_name_buf) < PATCH_NAME_MAX:
            _name_buf += NAME_CHARS[_name_i % len(NAME_CHARS)]
        need_redraw = True
        return
    if pmode == 'menu':
        name = _cur_sel_name()
        act = PMENU[pmenu_i]
        if act == "LOAD":
            toast("LOADED" if load_patch(name) else "LOAD FAILED")
        elif act == "SAVE OVER":
            toast("SAVED" if save_patch(name) else "SAVE FAILED")
        elif act == "RENAME":
            _start_name(name, rename_of=name)
            return
        elif act == "DELETE":
            toast("DELETED" if delete_patch(name) else "DELETE FAILED")
        pmode = 'list'
        need_redraw = True
        return
    sel = _cur_sel_name()
    if sel == "<NEW PATCH>":
        _start_name("")
    elif sel == "<RESCAN WT>":
        n = wt_rescan()
        apply_ab()
        toast("%d ON SD" % n if n else "NO SD FILES")
    else:
        pmode = 'menu'
        pmenu_i = 0
        need_redraw = True


def patch_back():
    global pmode, need_redraw
    pmode = 'list'
    need_redraw = True


# --------------------------------------------------------------------------
#  DRAW
# --------------------------------------------------------------------------

def draw():
    global need_redraw
    if not HAVE_BOARD or not DISPLAY_OK:
        need_redraw = False
        return
    d = amyboard.display
    try:
        d.fill(0)
        if is_patch_page():
            draw_patches(d)
        else:
            draw_grid(d)
        display_refresh()
    except Exception as e:
        print("draw failed:", e)
    need_redraw = False


def draw_splash(d):
    d.fill(0)
    d.text("AMYBOARD", 22, 34, C_BRIGHT)
    d.text("WAVETABLE", 18, 48, C_BRIGHT)
    d.text("4 VOICE / 8 OSC", 4, 68, C_DIM)
    d.text("%d TABLES" % wt_count(), 30, 84, C_DIM)


# --------------------------------------------------------------------------
#  SECTION 13 : INPUT
# --------------------------------------------------------------------------
#  encoder() and init_buttons() are called ONCE at boot, never inside the poll
#  loop -- calling them again resets the state before we read it.

def _goto_page(p):
    global page, cursor, editing, need_redraw, pmode
    # Leaving a page flushes a pending CV calibration to flash (deferred there
    # so sweeping the OFFSET knob does not hammer the card).
    cv_cal_save_if_dirty()
    page = p % N_PAGES
    cursor = 0
    editing = False
    pmode = 'list'
    if not is_patch_page() and PAGES[page][0] == "MATRIX":
        # Land on the MATRIX page showing the routing the cursor points at,
        # not a stale AMOUNT from the last time it was open.
        P["mx_amt"] = mx_get(int(P["mx_slot"]), DEST_IDS[int(P["mx_dest"])])
    need_redraw = True


def read_enc(i):
    if enc is None:
        return 0
    try:
        return enc.read(i)
    except Exception:
        return enc_last[i]


def read_btn(i=0):
    if enc is None:
        return False
    try:
        return bool(enc.button(i))
    except Exception:
        return False


def move_cursor(delta):
    """Move within THIS screen only.  A screen is a screen; changing it is a
    deliberate hold."""
    global cursor, need_redraw
    n = len(cur_rows())
    if n:
        cursor = int(clamp(cursor + delta, 0, n - 1))
    need_redraw = True


def edit_row(idx, delta):
    global need_redraw
    rows = cur_rows()
    if idx < 0 or idx >= len(rows):
        return
    # Mark, don't send: service_apply() flushes it once at the end of the tick
    # so a fast sweep is one coalesced apply, not one per detent (#2).
    mark_apply(bump(rows[idx], delta))
    need_redraw = True


def fire_action_row():
    """Run the row under the cursor if it is an ACTION ('a') row.

    Returns True if it fired, so the caller knows the click is spent.  Actions
    fire on the click itself rather than the click-then-turn dance every other
    row needs -- their value snaps back to 0 immediately, so on a single
    encoder they would otherwise look completely inert."""
    rows = cur_rows()
    if cursor < 0 or cursor >= len(rows):
        return False
    row = rows[cursor]
    if row[5] != 'a':
        return False
    fire_action(row[1])
    need_ui()
    return True


def poll_input():
    global editing, cursor, btn_last, btn_t, need_redraw
    if enc is None:
        return
    on_patches = is_patch_page()

    if page_mode:
        # Screen picker: encoder 0 scrolls, everything else is inert so a stray
        # nudge cannot edit the screen you are scrolling past.
        pos = read_enc(0)
        delta = pos - enc_last[0]
        if delta != 0:
            enc_last[0] = pos
            _goto_page(page + delta)
        # Keep the other baselines current, or the accumulated difference fires
        # as one big edit the moment you land.
        for i in range(1, 8):
            enc_last[i] = read_enc(i)
    elif n_enc >= 8 and not on_patches:
        rows = cur_rows()
        for i in range(8):
            pos = read_enc(i)
            delta = pos - enc_last[i]
            if delta != 0:
                enc_last[i] = pos
                if i < len(rows):
                    cursor = i
                    edit_row(i, delta)
    else:
        pos = read_enc(0)
        delta = pos - enc_last[0]
        if delta != 0:
            enc_last[0] = pos
            if on_patches:
                patch_turn(delta)
            elif editing:
                edit_row(cursor, delta)
            else:
                move_cursor(delta)

    b = read_btn(0)
    now = _now()
    if b and not btn_last:
        btn_t = now
        btn_last = True
    elif (not b) and btn_last:
        btn_last = False
        held_ms = _dt(now, btn_t)
        if held_ms > 700:
            if page_mode:
                _exit_page_mode()
            elif on_patches and pmode == 'name':
                _commit_name()
            elif on_patches and pmode != 'list':
                patch_back()
            else:
                _enter_page_mode()
        elif held_ms > 25:
            if page_mode:
                _exit_page_mode()
            elif on_patches:
                patch_click()
            elif fire_action_row():
                pass
            elif n_enc >= 8:
                # Nothing to do: all eight rows already have their own encoder,
                # and screen changes go through page mode.
                pass
            else:
                editing = not editing
                need_redraw = True


def _enter_page_mode():
    global page_mode, editing, pmode, need_redraw
    page_mode = True
    editing = False
    pmode = 'list'
    need_redraw = True


def _exit_page_mode():
    global page_mode, need_redraw
    page_mode = False
    need_redraw = True


# --------------------------------------------------------------------------
#  SECTION 14 : MIDI
# --------------------------------------------------------------------------
_midi_chans_seen = set()


def midi_cb(msg):
    try:
        if not msg:
            return
        st = msg[0]
        if st < 0x80:
            return
        ch = (st & 0x0F) + 1
        cmd = st & 0xF0
        if ch != int(P["mch"]):
            # A wrong channel is a silent drop by design -- but that silence
            # looks identical to "MIDI isn't reaching this sketch at all" from
            # the outside.  Print each distinct wrong channel ONCE (not per
            # message), so a controller stuck on another channel shows up
            # immediately instead of costing a debugging round trip.
            if ch not in _midi_chans_seen:
                _midi_chans_seen.add(ch)
                print("midi: channel %d ignored -- this synth listens on %d "
                      "(MIDI CH on the MIX page)" % (ch, int(P["mch"])))
            return
        if cmd == 0x90 and len(msg) > 2 and msg[2] > 0:
            note_on(msg[1], msg[2] / 127.0)
        elif cmd == 0x80 or (cmd == 0x90 and len(msg) > 2):
            note_off(msg[1])
        elif cmd == 0xB0 and len(msg) > 2:
            cc, v = msg[1], msg[2] / 127.0
            if cc == 74:                    # filter cutoff (standard)
                P["cutoff"] = 30.0 + v * v * 11970.0
                apply_head()
            elif cc == 71:                  # resonance (standard)
                P["reso"] = 0.5 + v * 15.5
                apply_head()
            elif cc == 1:                   # mod wheel -> OSC A/B position
                P["a_pos"] = v
                P["b_pos"] = v
                apply_ab()
            elif cc == 76:                  # the performance macro: unison detune
                P["uni_det"] = v * 50.0
                apply_unison()
            elif cc == 123:
                all_off()
            need_ui()
        elif cmd == 0xE0 and len(msg) > 2:
            bend = ((msg[2] << 7) | msg[1]) - 8192
            # Global: pitch_bend rides every osc's `bend` coefficient, which is
            # why freq coefs always re-assert it.
            _amy_send(pitch_bend=round(bend / 8192.0 * P["bend"] / 12.0, 4))
    except Exception as e:
        print("midi_cb:", e)


# --------------------------------------------------------------------------
#  SECTION 15 : ANALOGUE DRIFT
# --------------------------------------------------------------------------
#  A slow, continuous per-voice pitch wander, so a unison stack never sounds
#  perfectly locked.  Each voice follows its own sine at a deliberately
#  non-aligned rate: stepped random targets read as discrete little jumps,
#  which is the wrong texture entirely.
#
#  This is the ONLY thing in the sketch that touches AMY from loop(), it runs
#  at loop's own ~60 ms cadence (not audio rate), it sends at most 8 messages,
#  and it is skipped outright when DRIFT is 0.
DRIFT_RATES = [0.021, 0.034, 0.017, 0.028]
DRIFT_PHASE0 = [0.00, 0.30, 0.60, 0.10]
_drift_t = 0.0
_drift_was_on = False


def service_drift():
    global _drift_t, _drift_was_on
    amt = P["uni_drift"]
    if amt <= 0.0:
        if _drift_was_on:
            # Settle back to nominal exactly once, rather than leaving the last
            # wander baked into the tuning.
            for v in range(NVOICE):
                _drift_cents[v] = 0.0
            retune()
            _drift_was_on = False
        return
    _drift_was_on = True
    _drift_t += 0.06
    for v in range(NVOICE):
        ph = DRIFT_PHASE0[v] + _drift_t * DRIFT_RATES[v]
        _drift_cents[v] = math.sin(2.0 * math.pi * ph) * amt * 4.0
    retune()


# --------------------------------------------------------------------------
#  SECTION 16 : DIAGNOSTICS  (REPL only -- never called from loop())
# --------------------------------------------------------------------------

def wt_selftest(note=60, ms=400):
    """Is wave=WAVETABLE actually compiled into this firmware?

    -DAMY_WAVETABLE is a build flag.  It is on in AMY's own Makefile and
    setup.py, but the AMYboard firmware comes from the tulipcc tree, which this
    sketch cannot inspect -- so this measures it instead of guessing: play a
    note, read AMY's own rendered output back, and report the peak.  Near
    silence with WT_ENABLED True means the flag is missing; set WT_ENABLED
    False and everything else in the synth keeps working on a plain saw."""
    print("wt_selftest: WT_ENABLED=%s, wave id %d, %d tables"
          % (WT_ENABLED, W_WAVETABLE, wt_count()))
    peak = 0
    note_on(note, 1.0)
    t0 = _now()
    while _dt(_now(), t0) < ms:
        try:
            buf = amy.get_output_buffer()
            if buf:
                for s in array.array('h', buf):
                    a = s if s >= 0 else -s
                    if a > peak:
                        peak = a
        except Exception as e:
            print("wt_selftest: output buffer unavailable:", e)
            break
        time.sleep(0.01)
    note_off(note)
    print("wt_selftest: peak %d / 32767 (%.1f%%)" % (peak, peak / 327.67))
    if peak < 200:
        print("  -> SILENT.  Either this firmware has no -DAMY_WAVETABLE, or")
        print("     the selected table failed to load.  Try WT_ENABLED=False")
        print("     (then run boot()) to confirm the rest of the synth works.")
    else:
        print("  -> wavetable oscillators are rendering.")
    return peak


def wt_list():
    """Print the wavetable catalogue and which tables are resident in RAM."""
    print("catalogue (TABLE knob) -- root:", WT_ROOT or "(SD not scanned yet)")
    for i in range(len(WT_CATALOG)):
        name, path, builtin = WT_CATALOG[i]
        if callable(builtin):
            where = "generated (RAM preset %d)" % (WT_GEN_BASE + i)
        elif builtin is not None:
            where = "ROM preset %d" % builtin
        else:
            where = path
        live = ""
        if callable(builtin) and i in _wt_gen_loaded:
            live = "  [resident]"
        if path in _wt_slot_of:
            live = "  [RAM preset %d]" % _wt_slot_of[path]
        if path in _wt_failed:
            live = "  [FAILED]"
        print("  %2d  %-12s %s%s" % (i, name, where, live))
    print("%d/%d RAM slots in use" % (len(_wt_slot_of), WT_SLOTS))
    if _sd_files:
        print("SD browse list (WT LOAD page):")
        for i, (name, path) in enumerate(_sd_files):
            print("  %2d  %-12s %s" % (i, name, path))
    else:
        print("SD not scanned -- run wt_scan_sd() or SCAN SD on the WT LOAD page")


def wt_scan():
    """Scan the SD card from the REPL (same as SCAN SD on the WT LOAD page)."""
    n = wt_scan_sd()
    print("%d wavetable file(s) found on SD (root: %s)" % (n, WT_ROOT))
    for rel, path in _sd_files:
        print("  ", path)
    if n == 0:
        print("  none.  Try sd_ls() to see the raw card contents.")
    return n


_WAV_FMT_NAMES = {0x0001: "PCM int", 0x0003: "IEEE float", 0xFFFE: "extensible"}


def wt_wavinfo(path):
    """Print a WAV file's real format -- what the decoder sees.

    Use this when a load fails: it names the format tag, channels, bit depth
    and frame count, so you can tell at a glance whether a file is float,
    24-bit, stereo, too short, etc.  Reads only the header, loads nothing."""
    try:
        f = open(path, 'rb')
    except Exception as e:
        print("cannot open %s: %s" % (path, e))
        return
    try:
        fmt_tag, nch, sr, bits, dpos, dsize = _wav_read_header(f)
    except Exception as e:
        print("%s: not readable -- %s" % (path, e))
        f.close()
        return
    f.close()
    bytes_per = (bits + 7) // 8
    frames = dsize // (nch * bytes_per) if nch and bytes_per else 0
    cycles = frames // WT_CYCLE
    print("%s" % path)
    print("  format : 0x%04X (%s)" % (fmt_tag, _WAV_FMT_NAMES.get(fmt_tag, "?")))
    print("  channels %d, %d-bit, %d Hz" % (nch, bits, sr))
    print("  %d frames = %d wavetable cycles (of 256)" % (frames, cycles))
    ok = (fmt_tag in (0x0001, 0x0003)) and frames >= WT_MIN_SAMPLES
    print("  loadable: %s" % ("YES" if ok else "NO"))


def wt_try(path):
    """Attempt to decode + load a WAV from the REPL, printing the outcome.

    A direct way to test one file without going through the UI."""
    try:
        mono, sr, n = _wav_to_mono16(path)
        print("decoded OK: %d mono frames @ %d Hz (%d bytes 16-bit)"
              % (n, sr, len(mono)))
    except Exception as e:
        print("decode FAILED: %s" % e)


# --- CV diagnostics (REPL only) --------------------------------------------
_cv_cal_pts = []


def cv_read(samples=32, gap_ms=5):
    """Average the pitch jack (CV2) over many reads, for calibration."""
    total = 0.0
    n = 0
    for _ in range(samples):
        try:
            total += amyboard.cv_in(CV_PITCH_INPUT)
        except Exception as e:
            print("cv_read: cv_in() failed:", e)
            return None
        n += 1
        try:
            time.sleep_ms(gap_ms)
        except AttributeError:
            time.sleep(gap_ms / 1000.0)
    return total / n if n else None


def cv_cal(note=None, samples=32):
    """Fit BASE / TRIM / SCALE from two measured points.  cv_cal() clears.

    Hold a low note into the pitch jack, call cv_cal(<midi note>); hold a note
    2+ octaves away, call cv_cal(<that note>).  Prints the three CV_* constants
    to paste into the block at the top of the sketch (or dial in on CV CAL)."""
    global _cv_cal_pts
    if note is None:
        _cv_cal_pts = []
        print("CV cal: cleared. Hold a low note, then cv_cal(<note number>).")
        return
    v = cv_read(samples)
    if v is None:
        return
    _cv_cal_pts.append((v, float(note)))
    print("CV cal: point %d -- %.4f V = note %g" % (len(_cv_cal_pts), v, note))
    if len(_cv_cal_pts) < 2:
        print("  now hold a note 2+ octaves away and call cv_cal(<that note>).")
        return
    v0, n0 = _cv_cal_pts[0]
    v1, n1 = _cv_cal_pts[-1]
    if abs(v1 - v0) < 0.05:
        print("  points too close in voltage to fit -- use a wider interval.")
        return
    scale = ((n1 - n0) / 12.0) / (v1 - v0)
    base = n0 - 12.0 * scale * v0
    base_i = int(round(base))
    print("  CV_BASE_NOTE        = %d" % base_i)
    print("  CV_PITCH_TRIM_CENTS = %.1f" % ((base - base_i) * 100.0))
    print("  CV_PITCH_SCALE      = %.4f" % scale)


def cv_status():
    """Live look at both jacks -- the quickest check that CV is arriving."""
    try:
        g = amyboard.cv_in(CV_GATE_INPUT)
        v = amyboard.cv_in(CV_PITCH_INPUT)
    except Exception as e:
        print("cv_in() unavailable:", e)
        return
    print("CV%d gate  %+.3f V  (on>%.2f off<%.2f)  %s"
          % (CV_GATE_INPUT + 1, g, CV_GATE_ON, CV_GATE_OFF,
             "TRIGGERED" if g >= CV_GATE_ON else "idle"))
    print("CV%d pitch %+.3f V  raw -> %s  (trim %+.3fV, %s mode)"
          % (CV_PITCH_INPUT + 1, v, _note_name(cv_note_for(v)),
             cv_offset_volts(), CV_PITCH_MODE))


def dist_status():
    """Whether this build's DRIVE/FOLD run in the engine (native dist_*)."""
    if HAVE_DIST:
        print("distortion: native AMY dist_* (instant, per-note modulatable)")
    else:
        print("distortion: NOT in this build -- DRIVE/FOLD do nothing.")
        print("  update AMY to a build that includes the dist_* block.")
    for which in ("a", "b"):
        print("  OSC %s: drive %.2f  fold %s"
              % (which.upper(), _eff_osc_drive(which),
                 "on" if P[which + "_fold"] else "off"))
    print("  bus DRIVE page: drive %.2f fold %s bits %d rate %d"
          % (P["d_drive"], "on" if P["d_fold"] else "off",
             int(P["d_bits"]), int(P["d_rate"])))


def sd_ls(dirpath=None, depth=0):
    """Raw recursive listing of the SD card, for diagnosing an empty scan.

    Shows every file and folder (not just .wav) so you can confirm the card is
    mounted and see where your files actually live."""
    if dirpath is None:
        dirpath = _sd_card_root()
        if dirpath is None:
            print("No SD card mount found (tried tulip.root_dir()+'sd', /sd, "
                  "/flash, /user).")
            return
        print("SD root:", dirpath)
    for name, is_dir in _sd_iter(dirpath):
        print("  " * (depth + 1) + name + ("/" if is_dir else ""))
        if is_dir and depth < 3 and name not in _SD_SKIP and not name.startswith("."):
            sd_ls(dirpath + "/" + name, depth + 1)


def matrix_list():
    """Print every live routing, as the audio path sees it."""
    n = 0
    for scope in ('a', 'b', 'h'):
        for slot, dest, amt in mx_routings(scope):
            off, coef = mod_terms(slot, amt, DEST_UNIT[dest])
            print("  %s -> %-6s amt %+.2f  (coef %+.3f, const offset %+.3f, %s)"
                  % (MOD_SLOT_NAMES[slot], dest, amt, coef, off,
                     POLARITY[int(P["m%d_pol" % (slot + 1)])]))
            n += 1
    if n == 0:
        print("  (no routings)")
    return n


def status():
    print("mode      :", VOICE_MODES[int(P["vmode"])])
    print("voices    :", _vnote)
    print("tables    :", wt_name(P["a_wt"]), "/", wt_name(P["b_wt"]))
    print("patch     :", _cur_patch or "(unsaved)")
    try:
        print("render load: %.0f%%" % (amy.render_load() * 100.0))
    except Exception:
        pass
    matrix_list()


def cpu_status():
    try:
        print("render load: %.1f%%" % (amy.render_load() * 100.0))
    except Exception as e:
        print("render_load unavailable:", e)


def dsp(on=True):
    """Mute/unmute without touching the patch -- for A/B-ing CPU load."""
    _amy_send(bus=BUS, volume=round(P["vol"], 3) if on else 0.0)


# --------------------------------------------------------------------------
#  SECTION 17 : BOOT AND MAIN LOOP
# --------------------------------------------------------------------------

def boot_amy():
    """Bring AMY to a known state.  Called from boot() and from panic().

    Every OTHER synth is zeroed first: AMY can bring up default demo
    instruments at boot on several synth numbers -- including the ones this
    sketch claims -- independently of anything we send.  A synth with
    num_voices=0 cannot allocate a note, so this guarantees a clean slate."""
    for s in range(17):
        if s not in VOICE_SYNTHS:
            _amy_send(synth=s, num_voices=0)
    _amy_send(bus=BUS, volume=round(clamp(P["vol"], 0.0, 10.0), 3))


def boot():
    global enc, n_enc, need_redraw, HAVE_DIST

    # On the eight-encoder board encoder N edits row N, so a 9th row on any
    # page would be invisible to the knobs.  Cheap to check, and it fails
    # loudly at boot rather than silently stranding a parameter.
    for _nm, _rows in PAGES:
        if len(_rows) > 8:
            print("WARNING: page", _nm, "has", len(_rows), "rows (max 8)")

    amy.reset()                     # the one and only reset
    boot_amy()

    # Probe this AMY build's vocabulary ONCE.  The web REPL, the AMYboard
    # firmware and the desktop package are built from different snapshots; the
    # per-osc/bus distortion block is the newest thing this synth uses, so it
    # is the one most likely to be absent.  Skipping it up front keeps the
    # DRIVE/FOLD controls inert instead of crashing every voice build with
    # "Unknown keyword dist_clip".
    HAVE_DIST = _amy_knows("dist_clip")
    print("AMY %s -- distortion FX %s"
          % (getattr(amy, "version", "?"),
             "available" if HAVE_DIST
             else "NOT in this build (DRIVE/FOLD off -- update AMY firmware)"))

    # STARTUP CONTRACT: built-in tables only, no SD access.  The card is read
    # only later, on demand, from the WT LOAD page or when a patch names a
    # table -- so a missing or slow card can never stall or break boot.
    n = wt_builtins()
    print("wavetables: %d built-in (%s); load SD tables on the WT LOAD page"
          % (n, "/".join(nm for nm, _ in WT_BUILTIN)))
    wt_remember_selection()

    # CV calibration is restored BEFORE the voices are built, so the loaded
    # scale/offset are already in the freq coefficients the first build emits.
    try:
        if load_cv_cal():
            print("cv cal loaded: trim %+.3fV, base note %d"
                  % (cv_offset_volts(), CV_BASE_NOTE))
    except Exception as e:
        print("cv cal load failed:", e)

    try:
        build_all(full=True)
    except Exception as e:
        print("build_all failed:", e)
    try:
        apply_fx()
        apply_sys()
    except Exception as e:
        print("fx/sys failed:", e)
    # Register the CV gate/pitch mappings (audio-thread; harmless without a rig).
    try:
        setup_cv()
        print("CV in: %s mode, gate CV%d, pitch CV%d"
              % (CV_PITCH_MODE, CV_GATE_INPUT + 1, CV_PITCH_INPUT + 1))
    except Exception as e:
        print("setup_cv failed:", e)

    P["mx_amt"] = mx_get(int(P["mx_slot"]), DEST_IDS[int(P["mx_dest"])])

    if HAVE_BOARD:
        # NEITHER of these was guarded in an earlier AMYboard sketch, and an
        # exception in either aborted the whole of boot() -- which meant the
        # encoder setup and the MIDI callback below never ran either, and
        # `loop` never got defined: no display, no MIDI, no audio, all from one
        # unguarded call.
        try:
            init_display()
            if DISPLAY_OK:
                draw_splash(amyboard.display)
                display_refresh()
                time.sleep(1.5)
        except Exception as e:
            print("display init failed:", e)
        try:
            enc = amyboard.encoder()
            n_enc = getattr(enc, "encoders", 0)
            for i in range(min(8, max(1, n_enc))):
                enc_last[i] = enc.read(i)
            print("encoders:", getattr(enc, "type", "?"), n_enc)
        except Exception as e:
            print("encoder init failed:", e)
            enc = None

    # MIDI -- add_callback, never tulip.midi_callback(), which replaces the
    # system dispatcher and breaks everything else on the board.
    if HAVE_MIDI:
        try:
            midimod.add_callback(midi_cb)
        except Exception as e:
            print("midi callback failed:", e)

    print("AMYBOARD WAVETABLE ready -- %d voices on synths %s"
          % (NVOICE, VOICE_SYNTHS))
    print("REPL helpers: status() wt_scan() sd_ls() wt_wavinfo(p) cv_status()")
    need_redraw = True


boot()

_loop_fault = False
_scope_t = 0
_ui_t = 0
SCOPE_MS = 90           # the scope's own refresh cadence, MIX page only
UI_MS = 45              # #1: cap the interactive full-redraw rate (~22 fps)


def loop(*args):
    """AMYboard calls this roughly every 60 ms.  Accept the optional step arg.

    Nothing here is audio-rate.  The heaviest thing it can do is service_drift,
    which sends at most 8 messages and only when DRIFT is turned up."""
    global _loop_fault, _scope_t, _ui_t
    try:
        service_drift()
        poll_input()
        # #2: flush the tick's coalesced parameter changes as one burst BEFORE
        # drawing, so the frame we paint already reflects them.
        service_apply()
        now = _now()
        # #1: the full redraw (fill + grid + visual + a blocking full-panel
        # I2C flush) is throttled and decoupled from the loop rate.  A skipped
        # frame leaves need_redraw latched, so the FINAL state of a sweep always
        # lands -- input is never lost, only intermediate frames are dropped,
        # which keeps the OLED (a noise source into the audio path) quiet under
        # a fast knob spin.
        if need_redraw and _dt(now, _ui_t) >= UI_MS:
            _ui_t = now
            draw()                       # clears need_redraw
        elif not need_redraw and HAVE_BOARD and DISPLAY_OK and not is_patch_page():
            name = PAGES[page][0]
            if name == "MIX":
                # The scope has to keep moving even when nothing changed --
                # need_redraw only fires on USER input, and audio plays without
                # any.  Throttled and self-contained (it clears and redraws only
                # its own band), because bright OLED pixels couple noise into
                # the audio path on this hardware.
                if _dt(now, _scope_t) >= SCOPE_MS:
                    _scope_t = now
                    draw_scope(amyboard.display)
                    display_refresh()
            elif name == "CV CAL":
                # The CV jacks move without any user input, so a need_redraw-
                # gated readout would sit stale.  Only the pane is redrawn, and
                # the reading behind it is throttled (CV_VIS_MS).
                y0, h = vis_band()
                draw_vis_cvcal(amyboard.display, y0, h)
                display_refresh()
    except Exception as e:
        # loop() runs every ~60 ms: print the real traceback once, then stay
        # quiet, or a recurring fault floods the console and buries the one
        # report that would explain it.
        if not _loop_fault:
            _loop_fault = True
            print("loop failed:", e)
            try:
                import sys
                sys.print_exception(e)
            except Exception:
                pass
