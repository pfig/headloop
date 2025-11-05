-- HeadLoop v1.6
-- 4-head looper + Tape Recorder
--
-- K2: Change active head (short press)
-- K2+K3: Change screen page (press both together)
-- K3: Record control (context-dependent)
--   Page Main: Click: Record/Stop | Double-click: Overdub | Long press: Clear loop (fade)
--   Page Tape: Click: Tape rec/stop | Double-click: Tape overdub | Long press: Clear tape (3s fade)
-- E1: Change parameter (context-dependent)
--   Page Main: Head parameter (vol, pitch, pan, filters, delay, start, end)
--   Page Tape: Tape parameter (sends 1-4, volume, reverse, mute)
-- E2: Adjust value (coarse)
-- E3: Adjust value (fine)
--
-- Screen Pages (K2+K3 together to switch):
-- Page 1 (Main): Head control - volume, pitch, pan, filters, delay, start, end
-- Page 2 (Tape): Tape recorder - sends 1-4, volume, reverse, mute + rec/overdub controls
--
-- Grid (optional):
-- PAGE 1 (Main):
-- Row 1: Parameter selection (1-8: vol, pitch, pan, filt LP/HP, filt BP, dly, start, end)
-- Row 2: [1-4] Active head | [5] REC | [6] OVRD | [7] CLEAR | [8] RESET
-- Rows 3-6: Position display
-- Row 7: Mute heads 1-4
-- Row 8: Reverse heads 1-4 | [8] Switch to Tape page
--
-- PAGE 2 (Tape Recorder):
-- Row 1: [S1] [S2] [S3] [S4] Send levels for each head
-- Row 2: [VOL] [LEN] [REC] [OVR] [CLR] [REV] [MUTE] Controls
-- Rows 3-6: Tape position display
-- Row 7: Tape mode indicator
-- Row 8: [BACK] to main page
--
-- Parameters (PARAMS menu):
-- - Pitch mode (Semitones/Octaves)
-- - Reverb send + mix
-- - Delay time + feedback + mix
-- - Overdub level + feedback
-- - Clear fade time
-- - Tape FX on/off + wobble + saturation + age
-- - Tape Recorder: 4 sends + volume + length + controls
-- - 4 LFOs (sine/random) with speed, depth, destination
-- - MIDI device selection
-- - MIDI CC mapping per param
--
-- Parameters per head (9 params, E1 cycles all):
-- 1-8 on Grid: volume, pitch, pan, filter LP/HP, filter BP, delay, start, end
-- 9 E1 only: filter Q (resonance)

local softcut = require("softcut")
local g = grid.connect()
local mg = util.file_exists(_path.code .. "midigrid") and include "midigrid/lib/mg_128" or nil
local midi_device = nil
local midi_cc_params = {}

-- Constants
local MAX_LOOP_TIME = 60
local BUFFER_1 = 1
local NUM_HEADS = 4

-- LFO destinations
local lfo_destinations = {
  "None",
  "Vol 1", "Vol 2", "Vol 3", "Vol 4",
  "Pan 1", "Pan 2", "Pan 3", "Pan 4",
  "Start 1", "Start 2", "Start 3", "Start 4",
  "End 1", "End 2", "End 3", "End 4",
  "Pitch 1", "Pitch 2", "Pitch 3", "Pitch 4"
}

-- State
local recording = false
local loop_length = 0
local loop_exists = false
local active_head = 1
local active_param = 1
local rec_time = 0
local grid_device = nil
local k2_pressed = false
local k3_pressed = false
local k2_press_time = 0
local k3_press_time = 0
local k3_double_click_time = 0
local k3_double_click_threshold = 0.3
local pitch_mode = 1 -- 1 = semitones, 2 = octaves

-- E/ Message system
local message_text = ""
local message_time = 0
local message_duration = 2 -- seconds

-- Tape FX state
local tape_wobble_lfo1 = 0
local tape_wobble_lfo2 = 0
local tape_wobble_phase1 = 0
local tape_wobble_phase2 = 0
local tape_dropout_timer = 0
local tape_dropout_active = false
local tape_clock = nil

-- LFO state (4 LFOs)
local lfos = {}
for i = 1, 4 do
  lfos[i] = {
    phase = 0,
    value = 0,
    shape = 1, -- 1 = sine, 2 = random
    speed = 0.5,
    depth = 0,
    destination = 1, -- 1 = none, 2-21 = various params
    random_target = 0,
    random_current = 0
  }
end
local lfo_clock = nil

-- Tape Recorder state
local tape_recording = false
local tape_overdubbing = false
local tape_playing = false
local tape_exists = false
local tape_position = 0
local tape_length_recorded = 0
local tape_buffer_start = 5 -- Start at 5s in buffer 2 (after delay)
local tape_reverse = false
local tape_muted = false
local current_page = 1 -- 1 = main (grid), 2 = tape recorder (grid)
local screen_page = 1 -- 1 = main, 2 = tape (screen)
local tape_page_param = 1 -- Selected parameter on tape screen page (1-7)

-- Parameters per head
local params_list = {
  {name = "volume", min = 0, max = 2, default = 1.0},
  {name = "pitch", min = -24, max = 24, default = 0}, -- semitones or octaves depending on pitch_mode
  {name = "pan", min = -1, max = 1, default = 0}, -- -1 left, 0 center, 1 right
  {name = "filter_lp_hp", min = -1, max = 1, default = 0}, -- -1 HP, 0 none, 1 LP (E2)
  {name = "filter_bp", min = 0, max = 1, default = 0}, -- BP amount (E3)
  {name = "delay", min = 0, max = 1, default = 0}, -- delay send level
  {name = "start", min = 0, max = 1, default = 0.0},
  {name = "end", min = 0, max = 1, default = 1.0},
  {name = "filter_q", min = 0.1, max = 4, default = 0.5}, -- resonance (last, less used)
}

-- Head parameters
local heads = {}
for i = 1, NUM_HEADS do
  heads[i] = {
    voice = i + 1,
    enabled = true,
    muted = false,
    reverse = false,
    volume = 1.0,
    pitch = 0, -- semitones or octaves depending on pitch_mode
    rate = 1.0, -- calculated from pitch
    pan = (i - 2.5) * 0.4, -- spread heads in stereo
    filter_lp_hp = 0, -- -1 HP, 0 none, 1 LP
    filter_bp = 0, -- BP amount
    filter_q = 0.5, -- resonance
    filter_freq = 12000, -- filter frequency
    delay = 0, -- delay send
    start = 0.0,
    ending = 1.0,
    position = 0.0
  }
end

-- Convert pitch to rate (handles both semitones and octaves)
function pitch_to_rate(pitch_value)
  if pitch_mode == 2 then
    -- Octaves mode: convert octaves to semitones
    return 2 ^ pitch_value
  else
    -- Semitones mode
    return 2 ^ (pitch_value / 12)
  end
end

-- Get pitch min/max based on mode
function get_pitch_range()
  if pitch_mode == 2 then
    return -2, 2 -- -2 to +2 octaves
  else
    return -24, 24 -- -24 to +24 semitones
  end
end

-- E/ Message system
function show_message(text, duration)
  message_text = text
  message_time = util.time()
  message_duration = duration or 2
  redraw()
end

-- Grid functions
function grid_redraw()
  if grid_device == nil then return end
  
  grid_device:all(0)
  
  if current_page == 1 then
    -- PAGE 1: MAIN
    
    -- C/ SWAPPED: Parameter selection now on row 1 (first 8 params only)
    local max_grid_params = math.min(8, #params_list)
    for i = 1, max_grid_params do
      grid_device:led(i, 1, i == active_param and 15 or 4)
    end
    
    -- C/ SWAPPED: Row 2 - Active head selection (1-4) + Control buttons (5-8)
    for i = 1, NUM_HEADS do
      grid_device:led(i, 2, i == active_head and 15 or 4)
    end
    
    -- Control buttons (row 2, positions 5-8)
    -- Position 5: REC/STOP
    if recording and not loop_exists then
      grid_device:led(5, 2, 15) -- Recording - bright
    else
      grid_device:led(5, 2, 4) -- Not recording - dim
    end
    
    -- Position 6: OVERDUB
    if recording and loop_exists then
      grid_device:led(6, 2, 15) -- Overdubbing - bright
    elseif loop_exists then
      grid_device:led(6, 2, 8) -- Ready to overdub - medium
    else
      grid_device:led(6, 2, 2) -- No loop - very dim
    end
    
    -- Position 7: CLEAR LOOP
    if loop_exists then
      grid_device:led(7, 2, 10) -- Loop exists - medium-bright
    else
      grid_device:led(7, 2, 2) -- No loop - very dim
    end
    
    -- Position 8: RESET ALL HEADS
    grid_device:led(8, 2, 6) -- Always available - medium-dim
    
    -- Position indicator (rows 3-6) - unchanged
    for i = 1, NUM_HEADS do
      if loop_exists then
        local pos_col = util.clamp(math.floor(heads[i].position * 16) + 1, 1, 16)
        grid_device:led(pos_col, 2 + i, i == active_head and 15 or 6)
      end
    end
    
    -- C/ SWAPPED: Mute buttons now on row 7
    for i = 1, NUM_HEADS do
      local brightness = heads[i].muted and 4 or 15
      if i == active_head then brightness = heads[i].muted and 8 or 15 end
      grid_device:led(i, 7, brightness)
    end
    
    -- C/ SWAPPED: Reverse buttons now on row 8
    for i = 1, NUM_HEADS do
      local brightness = heads[i].reverse and 15 or 4
      if i == active_head then brightness = heads[i].reverse and 15 or 8 end
      grid_device:led(i, 8, brightness)
    end
    
    -- Add button to switch to tape page (row 8, column 8)
    grid_device:led(8, 8, 8)
    
  elseif current_page == 2 then
    -- PAGE 2: TAPE RECORDER
    
    -- Row 1: Send levels (pads 1-4)
    for i = 1, 4 do
      local level = params:get("tape_send_" .. i)
      local brightness = util.round(level * 15)
      grid_device:led(i, 1, brightness)
    end
    
    -- Row 2: Controls
    -- VOL indicator
    local vol_brightness = util.round(params:get("tape_volume") * 15)
    grid_device:led(1, 2, vol_brightness)
    
    -- LEN indicator
    local len = params:get("tape_length")
    local len_brightness = util.round(util.linlin(10, 300, 4, 15, len))
    grid_device:led(2, 2, len_brightness)
    
    -- REC button
    if tape_recording and not tape_overdubbing then
      grid_device:led(3, 2, 15) -- Recording
    else
      grid_device:led(3, 2, loop_exists and 4 or 2) -- Ready if loop exists
    end
    
    -- OVR button
    if tape_overdubbing then
      grid_device:led(4, 2, 15) -- Overdubbing
    elseif tape_exists then
      grid_device:led(4, 2, 8) -- Ready
    else
      grid_device:led(4, 2, 2) -- Unavailable
    end
    
    -- CLR button
    grid_device:led(5, 2, tape_exists and 10 or 2)
    
    -- REV button (reverse)
    if tape_reverse then
      grid_device:led(6, 2, 15) -- Active
    else
      grid_device:led(6, 2, tape_exists and 6 or 2) -- Available/unavailable
    end
    
    -- MUTE button
    if tape_muted then
      grid_device:led(7, 2, 4) -- Muted (dim)
    else
      grid_device:led(7, 2, tape_exists and 15 or 2) -- Active/unavailable
    end
    
    -- Rows 3-6: Position display
    if tape_exists and tape_length_recorded > 0 then
      -- Get current position (we'll update this via phase callback)
      local pos_percent = (tape_position - tape_buffer_start) / tape_length_recorded
      local pos_col = util.clamp(math.floor(pos_percent * 16) + 1, 1, 16)
      
      -- Draw position across 4 rows for visibility
      for row = 3, 6 do
        grid_device:led(pos_col, row, 15)
        -- Draw dimmer background
        for col = 1, 16 do
          if col ~= pos_col then
            grid_device:led(col, row, 2)
          end
        end
      end
    end
    
    -- Row 7: Tape mode indicator
    if tape_recording or tape_playing then
      for i = 1, 8 do
        grid_device:led(i, 7, tape_recording and 15 or 6)
      end
    end
    
    -- Row 8: Back button
    grid_device:led(1, 8, 10)
  end
  
  grid_device:refresh()
end

function grid_key(x, y, z)
  if z == 1 then
    if current_page == 1 then
      -- PAGE 1: MAIN
      
      -- C/ SWAPPED: Parameter selection now on row 1 (first 8 params only)
      local max_grid_params = math.min(8, #params_list)
      if y == 1 and x >= 1 and x <= max_grid_params then
        active_param = x
        grid_redraw()
        redraw()
      end
      
      -- C/ SWAPPED: Row 2 - Active head selection (1-4) + Control buttons (5-8)
      if y == 2 then
        if x >= 1 and x <= NUM_HEADS then
          -- Active head selection
          active_head = x
          grid_redraw()
          redraw()
        elseif x == 5 then
          -- REC/STOP button
          if not loop_exists and not recording then
            start_recording()
          elseif recording and not loop_exists then
            stop_recording()
          end
        elseif x == 6 then
          -- OVERDUB button
          if loop_exists and not recording then
            start_overdub()
          elseif recording and loop_exists then
            stop_overdub()
          end
        elseif x == 7 then
          -- CLEAR LOOP button
          if loop_exists then
            clear_loop()
          end
        elseif x == 8 then
          -- RESET ALL HEADS button
          reset_all_heads()
        end
      end
      
      -- Position display / head selection (rows 3-6) - unchanged
      if y >= 3 and y <= 6 and x >= 1 and x <= 16 then
        active_head = y - 2
        grid_redraw()
        redraw()
      end
      
      -- C/ SWAPPED: Mute toggles now on row 7
      if y == 7 and x >= 1 and x <= NUM_HEADS then
        heads[x].muted = not heads[x].muted
        update_head(x)
        grid_redraw()
        redraw()
      end
      
      -- C/ SWAPPED: Reverse toggles now on row 8
      if y == 8 then
        if x >= 1 and x <= NUM_HEADS then
          heads[x].reverse = not heads[x].reverse
          update_head(x)
          grid_redraw()
          redraw()
        elseif x == 8 then
          -- Switch to Tape page
          current_page = 2
          grid_redraw()
        end
      end
      
    elseif current_page == 2 then
      -- PAGE 2: TAPE RECORDER
      
      -- Row 1: Send levels (pads 1-4)
      if y == 1 and x >= 1 and x <= 4 then
        local send_param = "tape_send_" .. x
        local current = params:get(send_param)
        -- Cycle through levels: 0, 0.25, 0.5, 0.75, 1.0
        local levels = {0, 0.25, 0.5, 0.75, 1.0}
        local current_index = 1
        for i, v in ipairs(levels) do
          if math.abs(current - v) < 0.01 then
            current_index = i
            break
          end
        end
        local next_index = (current_index % #levels) + 1
        params:set(send_param, levels[next_index])
        grid_redraw()
      end
      
      -- Row 2: Controls
      if y == 2 then
        if x == 1 then
          -- VOL: cycle tape volume (0, 0.3, 0.5, 0.7, 1.0)
          local vol = params:get("tape_volume")
          local volumes = {0, 0.3, 0.5, 0.7, 1.0}
          local idx = 1
          for i, v in ipairs(volumes) do
            if math.abs(vol - v) < 0.01 then idx = i; break end
          end
          params:set("tape_volume", volumes[(idx % #volumes) + 1])
          grid_redraw()
        elseif x == 2 then
          -- LEN: cycle tape length (30, 60, 120, 180, 240, 300)
          local len = params:get("tape_length")
          local lengths = {30, 60, 120, 180, 240, 300}
          local idx = 1
          for i, v in ipairs(lengths) do
            if math.abs(len - v) < 5 then idx = i; break end
          end
          params:set("tape_length", lengths[(idx % #lengths) + 1])
          grid_redraw()
        elseif x == 3 then
          -- REC: Start/Stop recording
          if not tape_exists and not tape_recording and loop_exists then
            start_tape_recording()
          elseif tape_recording and not tape_overdubbing then
            stop_tape_recording()
          end
          grid_redraw()
        elseif x == 4 then
          -- OVR: Overdub
          if tape_exists and not tape_recording then
            start_tape_overdub()
          elseif tape_overdubbing then
            stop_tape_overdub()
          end
          grid_redraw()
        elseif x == 5 then
          -- CLR: Clear tape
          clear_tape()
          grid_redraw()
        elseif x == 6 then
          -- REV: Toggle reverse
          toggle_tape_reverse()
          grid_redraw()
        elseif x == 7 then
          -- MUTE: Toggle mute
          toggle_tape_mute()
          grid_redraw()
        end
      end
      
      -- Row 3-6: Position display (tap to jump)
      if y >= 3 and y <= 6 and tape_exists and x >= 1 and x <= 16 then
        local position_percent = (x - 1) / 15
        local new_pos = tape_buffer_start + (position_percent * tape_length_recorded)
        softcut.position(1, new_pos)
      end
      
      -- Row 8: Back to main page
      if y == 8 and x == 1 then
        current_page = 1
        grid_redraw()
      end
    end
  end
end

-- Initialize grid
function init_grid()
  if g.device then
    grid_device = g
    g.key = grid_key
  elseif mg then
    grid_device = mg
    mg.key = grid_key
  end
end

function init()
  -- Setup audio
  audio.level_cut(1.0)
  audio.level_adc_cut(1)
  
  -- Reverb - uses Norns system reverb (configure in SYSTEM > AUDIO)
  audio.level_cut_rev(0) -- Start with reverb send OFF
  
  -- Initialize grid
  init_grid()
  
  -- Setup recording voice (voice 1)
  softcut.enable(1, 1)
  softcut.buffer(1, BUFFER_1)
  softcut.level(1, 1.0)
  softcut.level_input_cut(1, 1, 1.0)
  softcut.level_input_cut(2, 1, 1.0)
  softcut.pan(1, 0)
  softcut.play(1, 0)
  softcut.rate(1, 1)
  softcut.rec(1, 0)
  softcut.rec_level(1, 1)
  softcut.pre_level(1, 0)
  softcut.position(1, 0)
  softcut.loop_start(1, 0)
  softcut.loop_end(1, MAX_LOOP_TIME)
  softcut.loop(1, 0)
  softcut.fade_time(1, 0.1)
  softcut.phase_quant(1, 0.05) -- Enable phase tracking for tape recorder
  
  -- Setup delay (using voice 6 as delay)
  softcut.enable(6, 1)
  softcut.buffer(6, 2)
  softcut.level(6, 0.3) -- mix - controlled by delay_mix param
  softcut.loop(6, 1)
  softcut.loop_start(6, 0)
  softcut.loop_end(6, 0.375) -- delay time - controlled by delay_time param
  softcut.position(6, 0)
  softcut.play(6, 1)
  softcut.rate(6, 1)
  softcut.rec(6, 1)
  softcut.rec_level(6, 1)
  softcut.pre_level(6, 0.5) -- feedback - controlled by delay_feedback param
  softcut.fade_time(6, 0.05)
  softcut.pan(6, 0)
  
  
  -- Setup playback heads (voices 2-5)
  for i = 1, NUM_HEADS do
    local v = heads[i].voice
    softcut.enable(v, 1)
    softcut.buffer(v, BUFFER_1)
    softcut.level(v, heads[i].volume)
    softcut.pan(v, heads[i].pan)
    
    -- Audio routing: send to outputs
    softcut.level_slew_time(v, 0.1)
    
    -- Send to delay voice (6)
    softcut.level_cut_cut(v, 6, 0)
    
    -- Setup filters
    softcut.post_filter_dry(v, 1.0)
    softcut.post_filter_lp(v, 0)
    softcut.post_filter_hp(v, 0)
    softcut.post_filter_bp(v, 0)
    softcut.post_filter_br(v, 0)
    softcut.post_filter_fc(v, 12000)
    softcut.post_filter_rq(v, 2.0)
    
    softcut.play(v, 0)
    softcut.rate(v, heads[i].rate)
    softcut.rec(v, 0)
    softcut.pre_level(v, 0)
    softcut.position(v, 0)
    softcut.loop_start(v, 0)
    softcut.loop_end(v, 1)
    softcut.loop(v, 1)
    softcut.fade_time(v, 0.01)
    
    softcut.phase_quant(v, 0.05)
    softcut.event_phase(function(v_idx, phase)
      -- Handle tape recorder (voice 1)
      if v_idx == 1 and tape_exists then
        tape_position = phase
        if current_page == 2 then
          grid_redraw()
        end
      end
      
      -- Handle playback heads (voices 2-5)
      if v_idx > 1 and v_idx <= NUM_HEADS + 1 then
        local h_idx = v_idx - 1
        local h = heads[h_idx]
        if loop_exists and h.ending > h.start then
          local loop_len = (h.ending - h.start) * loop_length
          h.position = (phase - h.start * loop_length) / loop_len
        end
        if current_page == 1 then
          grid_redraw()
        end
        redraw()
      end
    end)
  end
  
  -- Setup parameters
  params:add_separator("HeadLoop")
  
  -- Pitch mode
  params:add_option("pitch_mode", "Pitch Mode", {"Semitones", "Octaves"}, 1)
  params:set_action("pitch_mode", function(x)
    pitch_mode = x
    -- Clamp all head pitch values to new range
    local min_pitch, max_pitch = get_pitch_range()
    for i = 1, NUM_HEADS do
      heads[i].pitch = util.clamp(heads[i].pitch, min_pitch, max_pitch)
      if loop_exists then
        update_head(i)
      end
    end
    redraw()
  end)
  
  -- Reverb (uses Norns system reverb - configure in SYSTEM > AUDIO)
  params:add_separator("Reverb")
  params:add_option("reverb_enabled", "Reverb Send", {"Off", "On"}, 1)
  params:set_action("reverb_enabled", function(x)
    if x == 2 then
      audio.level_cut_rev(params:get("reverb_mix"))
    else
      audio.level_cut_rev(0)
    end
  end)
  
  params:add_control("reverb_mix", "Reverb Mix", controlspec.new(0, 1, 'lin', 0.01, 0.35, ''))
  params:set_action("reverb_mix", function(x)
    if params:get("reverb_enabled") == 2 then
      audio.level_cut_rev(x)
    end
  end)
  
  -- Delay settings
  params:add_separator("Delay")
  params:add_control("delay_time", "Delay Time", controlspec.new(0.01, 2, 'exp', 0.01, 0.375, 's'))
  params:set_action("delay_time", function(x)
    softcut.loop_end(6, x)
  end)
  
  params:add_control("delay_feedback", "Delay Feedback", controlspec.new(0, 0.95, 'lin', 0.01, 0.5, ''))
  params:set_action("delay_feedback", function(x)
    softcut.pre_level(6, x)
  end)
  
  params:add_control("delay_mix", "Delay Mix", controlspec.new(0, 1, 'lin', 0.01, 0.3, ''))
  params:set_action("delay_mix", function(x)
    softcut.level(6, x)
  end)
  
  -- Overdub settings
  params:add_separator("Overdub")
  params:add_control("overdub_level", "Overdub Level", controlspec.new(0, 1, 'lin', 0.01, 1.0, ''))
  params:add_control("overdub_feedback", "Overdub Feedback", controlspec.new(0, 1, 'lin', 0.01, 1.0, ''))
  
  -- Clear/Fade settings
  params:add_separator("Clear Loop")
  params:add_control("clear_fade_time", "Clear Fade Time", controlspec.new(0, 5, 'lin', 0.1, 1.0, 's'))
  
  -- Tape FX
  params:add_separator("Tape FX")
  params:add_option("tape_enabled", "Tape FX", {"Off", "On"}, 1)
  params:set_action("tape_enabled", function(x)
    if x == 2 then
      start_tape_fx()
    else
      stop_tape_fx()
    end
  end)
  
  params:add_control("tape_wobble", "Wobble", controlspec.new(0, 1, 'lin', 0.01, 0.3, ''))
  params:add_control("tape_sat", "Saturation", controlspec.new(0, 1, 'lin', 0.01, 0.2, ''))
  -- Note: tape_hiss removed (voice 7 doesn't exist, max 6 voices in softcut)
  params:add_control("tape_age", "Age (Dropout)", controlspec.new(0, 1, 'lin', 0.01, 0.0, ''))
  
  -- Tape Recorder
  params:add_separator("Tape Recorder")
  
  -- Send levels for each head to tape
  for i = 1, NUM_HEADS do
    params:add_control("tape_send_" .. i, "Tape Send Head " .. i, 
      controlspec.new(0, 1, 'lin', 0.01, 0, ''))
    params:set_action("tape_send_" .. i, function(x)
      if tape_recording or tape_playing then
        softcut.level_cut_cut(heads[i].voice, 1, x)
      end
    end)
  end
  
  -- Tape playback volume
  params:add_control("tape_volume", "Tape Volume", controlspec.new(0, 1, 'lin', 0.01, 0.7, ''))
  params:set_action("tape_volume", function(x)
    if tape_playing and not recording then
      softcut.level(1, x)
    end
  end)
  
  -- Tape max length
  params:add_control("tape_length", "Tape Length", controlspec.new(10, 300, 'lin', 1, 120, 's'))
  params:set_action("tape_length", function(x)
    if not tape_recording then
      -- Can only change when not recording
      if tape_exists then
        softcut.loop_end(1, tape_buffer_start + math.min(x, tape_length_recorded))
      end
    end
  end)
  
  -- LFOs (4 independent LFOs)
  for i = 1, 4 do
    params:add_separator("LFO " .. i)
    
    params:add_option("lfo" .. i .. "_shape", "LFO" .. i .. " Shape", {"Sine", "Random"}, 1)
    
    params:add_control("lfo" .. i .. "_speed", "LFO" .. i .. " Speed", 
      controlspec.new(0.01, 20, 'exp', 0.01, 0.5, 'Hz'))
    
    params:add_control("lfo" .. i .. "_depth", "LFO" .. i .. " Depth", 
      controlspec.new(0, 1, 'lin', 0.01, 0, ''))
    
    params:add_option("lfo" .. i .. "_dest", "LFO" .. i .. " Destination", 
      lfo_destinations, 1)
  end
  
  -- Start LFO clock
  start_lfo_clock()
  
  -- MIDI device
  params:add_option("midi_device", "MIDI Device", {"None", "1", "2", "3", "4"}, 1)
  params:set_action("midi_device", function(x)
    if x > 1 then
      midi_device = midi.connect(x - 1)
      midi_device.event = midi_event
    else
      midi_device = nil
    end
  end)
  
  -- MIDI CC Mappings for active head
  params:add_separator("MIDI CC Mapping")
  params:add_number("cc_volume", "CC Volume", 0, 127, 1)
  params:set_action("cc_volume", function() update_midi_mappings() end)
  params:add_number("cc_pitch", "CC Pitch", 0, 127, 2)
  params:set_action("cc_pitch", function() update_midi_mappings() end)
  params:add_number("cc_pan", "CC Pan", 0, 127, 3)
  params:set_action("cc_pan", function() update_midi_mappings() end)
  params:add_number("cc_filter_lp_hp", "CC Filter LP/HP", 0, 127, 4)
  params:set_action("cc_filter_lp_hp", function() update_midi_mappings() end)
  params:add_number("cc_filter_bp", "CC Filter BP", 0, 127, 5)
  params:set_action("cc_filter_bp", function() update_midi_mappings() end)
  params:add_number("cc_filter_q", "CC Filter Q", 0, 127, 6)
  params:set_action("cc_filter_q", function() update_midi_mappings() end)
  params:add_number("cc_delay", "CC Delay", 0, 127, 7)
  params:set_action("cc_delay", function() update_midi_mappings() end)
  params:add_number("cc_start", "CC Start", 0, 127, 8)
  params:set_action("cc_start", function() update_midi_mappings() end)
  params:add_number("cc_end", "CC End", 0, 127, 9)
  params:set_action("cc_end", function() update_midi_mappings() end)
  
  -- Tape MIDI CC mappings
  params:add_separator("MIDI CC Tape")
  params:add_number("cc_tape_send_1", "CC Tape Send H1", 0, 127, 10)
  params:set_action("cc_tape_send_1", function() update_midi_mappings() end)
  params:add_number("cc_tape_send_2", "CC Tape Send H2", 0, 127, 11)
  params:set_action("cc_tape_send_2", function() update_midi_mappings() end)
  params:add_number("cc_tape_send_3", "CC Tape Send H3", 0, 127, 12)
  params:set_action("cc_tape_send_3", function() update_midi_mappings() end)
  params:add_number("cc_tape_send_4", "CC Tape Send H4", 0, 127, 13)
  params:set_action("cc_tape_send_4", function() update_midi_mappings() end)
  params:add_number("cc_tape_volume", "CC Tape Volume", 0, 127, 14)
  params:set_action("cc_tape_volume", function() update_midi_mappings() end)
  
  -- Tape MIDI Note mappings
  params:add_separator("MIDI Note Tape")
  params:add_number("note_tape_rec", "Note Tape Rec/Stop", 0, 127, 60)
  params:add_number("note_tape_overdub", "Note Tape Overdub", 0, 127, 61)
  params:add_number("note_tape_clear", "Note Tape Clear", 0, 127, 62)
  params:add_number("note_tape_mute", "Note Tape Mute", 0, 127, 63)
  params:add_number("note_tape_reverse", "Note Tape Reverse", 0, 127, 64)
  
  -- Initialize CC mappings
  update_midi_mappings()
  
  redraw()
end

function update_midi_mappings()
  midi_cc_params = {
    [params:get("cc_volume")] = "volume",
    [params:get("cc_pitch")] = "pitch",
    [params:get("cc_pan")] = "pan",
    [params:get("cc_filter_lp_hp")] = "filter_lp_hp",
    [params:get("cc_filter_bp")] = "filter_bp",
    [params:get("cc_filter_q")] = "filter_q",
    [params:get("cc_delay")] = "delay",
    [params:get("cc_start")] = "start",
    [params:get("cc_end")] = "end",
    [params:get("cc_tape_send_1")] = "tape_send_1",
    [params:get("cc_tape_send_2")] = "tape_send_2",
    [params:get("cc_tape_send_3")] = "tape_send_3",
    [params:get("cc_tape_send_4")] = "tape_send_4",
    [params:get("cc_tape_volume")] = "tape_volume"
  }
end

-- Tape FX functions
function start_tape_fx()
  if tape_clock then
    clock.cancel(tape_clock)
  end
  
  tape_clock = clock.run(function()
    while true do
      clock.sleep(0.05) -- 20Hz update rate
      
      local wobble_amt = params:get("tape_wobble")
      local age_amt = params:get("tape_age")
      
      if wobble_amt > 0 then
        -- Two random LFOs for wow and flutter
        tape_wobble_phase1 = tape_wobble_phase1 + (0.3 + math.random() * 0.4) * wobble_amt
        tape_wobble_phase2 = tape_wobble_phase2 + (0.8 + math.random() * 1.2) * wobble_amt
        
        tape_wobble_lfo1 = math.sin(tape_wobble_phase1) * wobble_amt * 0.015
        tape_wobble_lfo2 = math.sin(tape_wobble_phase2) * wobble_amt * 0.008
        
        -- Apply wobble to all playback heads
        for i = 1, NUM_HEADS do
          if loop_exists and not heads[i].muted then
            local v = heads[i].voice
            local wobble = tape_wobble_lfo1 + tape_wobble_lfo2
            local base_rate = heads[i].rate
            local final_rate = base_rate * (1 + wobble)
            if heads[i].reverse then final_rate = -final_rate end
            softcut.rate(v, final_rate)
          end
        end
      end
      
      -- Age dropout simulation
      if age_amt > 0 then
        if not tape_dropout_active then
          -- Random chance to start dropout
          if math.random() < age_amt * 0.02 then
            tape_dropout_active = true
            tape_dropout_timer = math.random(2, 10) -- 2-10 frames
          end
        else
          tape_dropout_timer = tape_dropout_timer - 1
          
          -- Apply dropout (reduce volume)
          for i = 1, NUM_HEADS do
            if loop_exists then
              local v = heads[i].voice
              local dropout_level = heads[i].muted and 0 or heads[i].volume * 0.3
              softcut.level(v, dropout_level)
            end
          end
          
          if tape_dropout_timer <= 0 then
            tape_dropout_active = false
            -- Restore volumes
            for i = 1, NUM_HEADS do
              if loop_exists then
                update_head(i)
              end
            end
          end
        end
      end
      
      -- Apply saturation (subtle drive on pre_level)
      local sat_amt = params:get("tape_sat")
      if sat_amt > 0 then
        for i = 1, NUM_HEADS do
          if loop_exists then
            local v = heads[i].voice
            -- Increase pre_level slightly for saturation effect
            softcut.pre_level(v, sat_amt * 0.15)
          end
        end
      end
      
      -- Note: tape_hiss removed (voice 7 doesn't exist)
    end
  end)
end

function stop_tape_fx()
  if tape_clock then
    clock.cancel(tape_clock)
    tape_clock = nil
  end
  
  -- Reset all heads to normal
  for i = 1, NUM_HEADS do
    if loop_exists then
      update_head(i)
    end
  end
end

-- Tape Recorder functions
function start_tape_recording()
  if loop_exists and not recording then -- Can't use voice 1 if main recording active
    tape_recording = true
    tape_overdubbing = false
    tape_playing = true
    tape_exists = false
    tape_length_recorded = 0
    rec_time = util.time() -- Initialize rec_time to start counter from zero
    
    -- Configure voice 1 for tape recording
    softcut.buffer(1, 2) -- Use buffer 2
    softcut.position(1, tape_buffer_start)
    softcut.loop_start(1, tape_buffer_start)
    softcut.loop_end(1, tape_buffer_start + params:get("tape_length"))
    softcut.loop(1, 0) -- No loop during initial recording
    softcut.rec(1, 1)
    softcut.rec_level(1, 1)
    softcut.pre_level(1, 0) -- No feedback during initial recording
    softcut.play(1, 1)
    softcut.rate(1, 1)
    softcut.level(1, 0) -- Mute during recording
    softcut.pan(1, 0)
    
    -- Enable sends from heads to tape
    update_tape_sends()
    
    show_message("TAPE REC", 1.5)
  end
end

function stop_tape_recording()
  if tape_recording and not tape_overdubbing then
    tape_recording = false
    -- Get the actual recorded length
    tape_length_recorded = util.time() - rec_time -- or track via position
    -- Safer: read current position
    local current_pos = softcut.query_position(1)
    if current_pos then
      tape_length_recorded = current_pos - tape_buffer_start
    else
      tape_length_recorded = 10 -- fallback
    end
    tape_exists = true
    
    -- Configure for playback
    softcut.rec(1, 0)
    softcut.loop(1, 1)
    softcut.loop_end(1, tape_buffer_start + tape_length_recorded)
    softcut.level(1, params:get("tape_volume"))
    softcut.position(1, tape_buffer_start) -- Reset to start
    
    show_message("TAPE STOP", 1.5)
  end
end

function start_tape_overdub()
  if tape_exists and not tape_recording and not recording then
    tape_recording = true
    tape_overdubbing = true
    tape_playing = true
    
    -- Enable overdub
    softcut.rec(1, 1)
    softcut.rec_level(1, 1)
    softcut.pre_level(1, params:get("overdub_feedback")) -- Use same feedback as main loop
    softcut.play(1, 1)
    softcut.level(1, params:get("tape_volume"))
    
    -- Enable sends
    update_tape_sends()
    
    show_message("TAPE OVRD", 1.5)
  end
end

function stop_tape_overdub()
  if tape_recording and tape_overdubbing then
    tape_recording = false
    tape_overdubbing = false
    
    -- Back to playback only
    softcut.rec(1, 0)
    softcut.pre_level(1, 0)
    
    show_message("OVRD STOP", 1.5)
  end
end

function clear_tape()
  if tape_exists then
    show_message("TAPE FADE", 1.5)
    
    -- Fade out over 3 seconds
    local fade_time = 3.0
    local steps = 30
    local step_duration = fade_time / steps
    local initial_level = params:get("tape_volume")
    
    clock.run(function()
      for i = 1, steps do
        local fade_amount = 1 - (i / steps)
        local current_level = initial_level * fade_amount
        softcut.level(1, tape_muted and 0 or current_level)
        clock.sleep(step_duration)
      end
      
      -- After fade out, clear everything
      tape_recording = false
      tape_overdubbing = false
      tape_playing = false
      tape_exists = false
      tape_length_recorded = 0
      tape_reverse = false
      tape_muted = false
      
      -- Stop voice 1
      softcut.play(1, 0)
      softcut.rec(1, 0)
      softcut.level(1, 0)
      
      -- Disable sends
      for i = 1, NUM_HEADS do
        softcut.level_cut_cut(heads[i].voice, 1, 0)
      end
      
      show_message("TAPE CLR", 1.5)
      redraw()
    end)
  end
end

function update_tape_sends()
  -- Update send levels from each head to tape (voice 1)
  for i = 1, NUM_HEADS do
    local v = heads[i].voice
    local send_level = params:get("tape_send_" .. i)
    softcut.level_cut_cut(v, 1, send_level)
  end
end

function toggle_tape_playback()
  if tape_exists and not recording then
    tape_playing = not tape_playing
    if tape_playing then
      softcut.play(1, 1)
      softcut.level(1, tape_muted and 0 or params:get("tape_volume"))
      show_message("TAPE PLAY", 1)
    else
      softcut.play(1, 0)
      show_message("TAPE MUTE", 1)
    end
  end
end

function toggle_tape_reverse()
  if tape_exists and not recording then
    tape_reverse = not tape_reverse
    local rate = tape_reverse and -1 or 1
    softcut.rate(1, rate)
    show_message(tape_reverse and "TAPE REV" or "TAPE FWD", 1)
  end
end

function toggle_tape_mute()
  if tape_exists and not recording then
    tape_muted = not tape_muted
    local level = tape_muted and 0 or params:get("tape_volume")
    -- Add 1s fade time to avoid click
    softcut.level_slew_time(1, 1.0)
    softcut.level(1, level)
    show_message(tape_muted and "TAPE MUTE" or "TAPE ON", 1)
  end
end

function update_tape_playback()
  -- Update tape level and rate based on current state
  if tape_playing and not recording then
    local level = tape_muted and 0 or params:get("tape_volume")
    local rate = tape_reverse and -1 or 1
    softcut.level(1, level)
    softcut.rate(1, rate)
  end
end

-- LFO functions
function start_lfo_clock()
  if lfo_clock then
    clock.cancel(lfo_clock)
  end
  
  lfo_clock = clock.run(function()
    while true do
      clock.sleep(1/30) -- 30Hz update rate
      
      for i = 1, 4 do
        local lfo = lfos[i]
        local depth = params:get("lfo" .. i .. "_depth")
        local speed = params:get("lfo" .. i .. "_speed")
        local shape = params:get("lfo" .. i .. "_shape")
        local dest = params:get("lfo" .. i .. "_dest")
        
        if depth > 0 and dest > 1 then
          -- Update LFO phase
          lfo.phase = lfo.phase + (speed / 30)
          if lfo.phase >= 1 then
            lfo.phase = lfo.phase - 1
          end
          
          -- Calculate LFO value based on shape
          if shape == 1 then
            -- Sine wave
            lfo.value = math.sin(lfo.phase * math.pi * 2)
          else
            -- Random (sample & hold)
            if lfo.phase < 0.033 then -- New random value at start of cycle
              lfo.random_target = (math.random() * 2) - 1
            end
            -- Smooth interpolation to target
            lfo.random_current = lfo.random_current + (lfo.random_target - lfo.random_current) * 0.1
            lfo.value = lfo.random_current
          end
          
          -- Apply LFO to destination
          apply_lfo(i, dest, lfo.value * depth)
        end
      end
      
      redraw()
    end
  end)
end

function apply_lfo(lfo_idx, dest, amount)
  if not loop_exists then return end
  
  -- Destination mapping: 1=None, 2-5=Vol, 6-9=Pan, 10-13=Start, 14-17=End, 18-21=Pitch
  if dest >= 2 and dest <= 5 then
    -- Volume 1-4
    local head = dest - 1
    local base = heads[head].volume
    local modulated = util.clamp(base + (amount * 1.0), 0, 2)
    softcut.level(heads[head].voice, heads[head].muted and 0 or modulated)
    
  elseif dest >= 6 and dest <= 9 then
    -- Pan 1-4
    local head = dest - 5
    local base = heads[head].pan
    local modulated = util.clamp(base + (amount * 0.5), -1, 1)
    softcut.pan(heads[head].voice, modulated)
    
  elseif dest >= 10 and dest <= 13 then
    -- Start 1-4
    local head = dest - 9
    local base = heads[head].start
    local modulated = util.clamp(base + (amount * 0.3), 0, heads[head].ending - 0.01)
    softcut.loop_start(heads[head].voice, modulated * loop_length)
    
  elseif dest >= 14 and dest <= 17 then
    -- End 1-4
    local head = dest - 13
    local base = heads[head].ending
    local modulated = util.clamp(base + (amount * 0.3), heads[head].start + 0.01, 1)
    softcut.loop_end(heads[head].voice, modulated * loop_length)
    
  elseif dest >= 18 and dest <= 21 then
    -- Pitch 1-4
    local head = dest - 17
    local base = heads[head].pitch
    local modulation_range = pitch_mode == 2 and 1 or 12 -- 1 octave or 12 semitones
    local min_pitch, max_pitch = get_pitch_range()
    local modulated = util.clamp(base + (amount * modulation_range), min_pitch, max_pitch)
    local rate = pitch_to_rate(modulated)
    local final_rate = heads[head].reverse and -rate or rate
    softcut.rate(heads[head].voice, final_rate)
  end
end

-- Reverb modulation clock (BigSky-style shimmer and movement)

function start_recording()
  -- Stop tape recorder if active (shares voice 1)
  if tape_recording or tape_playing then
    if tape_recording then
      if tape_overdubbing then
        stop_tape_overdub()
      else
        stop_tape_recording()
      end
    end
    tape_playing = false
  end
  
  -- Configure voice 1 for main recording
  softcut.buffer(1, BUFFER_1) -- Main loop buffer
  softcut.loop_start(1, 0)
  softcut.loop_end(1, MAX_LOOP_TIME)
  softcut.loop(1, 0)
  softcut.pre_level(1, 0)
  softcut.rec_level(1, 1)
  softcut.level(1, 1.0)
  
  recording = true
  rec_time = util.time()
  loop_length = 0
  softcut.rec(1, 1)
  softcut.play(1, 1)
  softcut.position(1, 0)
  
  for i = 1, NUM_HEADS do
    softcut.play(heads[i].voice, 0)
  end
  
  redraw()
end

function stop_recording()
  recording = false
  loop_length = util.time() - rec_time
  loop_exists = true
  
  softcut.rec(1, 0)
  softcut.play(1, 0)
  
  -- Setup all heads to play the loop
  for i = 1, NUM_HEADS do
    local v = heads[i].voice
    local h = heads[i]
    
    -- Distribute heads evenly across the loop
    h.start = (i - 1) * 0.25
    h.ending = i * 0.25
    h.pitch = 0
    h.rate = 1.0
    h.muted = false
    h.reverse = false
    h.pan = (i - 2.5) * 0.4 -- reset to default spread
    h.filter_lp_hp = 0 -- reset filter LP/HP
    h.filter_bp = 0 -- reset filter BP
    h.filter_q = 0.5 -- reset resonance
    h.delay = 0 -- reset delay
    
    update_head(i)
    
    local offset = h.start * loop_length
    softcut.position(v, offset)
    softcut.play(v, 1)
  end
  
  grid_redraw()
  redraw()
end

function start_overdub()
  recording = true
  softcut.rec(1, 1)
  softcut.play(1, 0) -- Don't play voice 1 during overdub to avoid doubling
  softcut.pre_level(1, params:get("overdub_feedback")) -- Use feedback param
  softcut.rec_level(1, params:get("overdub_level")) -- Use level param
  softcut.loop(1, 1)
  softcut.loop_start(1, 0)
  softcut.loop_end(1, loop_length)
  
  redraw()
end

function stop_overdub()
  recording = false
  softcut.rec(1, 0)
  softcut.play(1, 0)
  softcut.pre_level(1, 0)
  
  redraw()
end

function reset_all_heads()
  if not loop_exists then return end
  
  -- Reset all heads to initial loop parameters
  for i = 1, NUM_HEADS do
    local v = heads[i].voice
    local h = heads[i]
    
    -- Reset to start parameters
    h.start = (i - 1) * 0.25
    h.ending = i * 0.25
    h.pitch = 0
    h.rate = 1.0
    h.muted = false
    h.reverse = false
    h.pan = (i - 2.5) * 0.4 -- reset to default spread
    h.filter_lp_hp = 0 -- reset filter LP/HP
    h.filter_bp = 0 -- reset filter BP
    h.filter_q = 0.5 -- reset resonance
    h.delay = 0 -- reset delay
    h.volume = 1.0 -- reset volume
    
    update_head(i)
    
    -- Reset position
    local offset = h.start * loop_length
    softcut.position(v, offset)
  end
  
  grid_redraw()
  redraw()
end

function clear_loop()
  local fade_time = params:get("clear_fade_time")
  
  if fade_time > 0 then
    -- Fade out all heads gradually
    clock.run(function()
      local steps = 20
      local step_time = fade_time / steps
      
      for step = 1, steps do
        local fade = 1 - (step / steps)
        
        -- Fade out all playback heads
        for i = 1, NUM_HEADS do
          if not heads[i].muted then
            softcut.level(heads[i].voice, heads[i].volume * fade)
          end
        end
        
        clock.sleep(step_time)
      end
      
      -- Now actually stop everything
      recording = false
      loop_exists = false
      loop_length = 0
      
      softcut.rec(1, 0)
      softcut.play(1, 0)
      
      for i = 1, NUM_HEADS do
        softcut.play(heads[i].voice, 0)
        softcut.level(heads[i].voice, heads[i].volume) -- Restore volume for next loop
        
        -- Reset all head parameters to defaults
        heads[i].pitch = 0
        heads[i].rate = 1.0
        heads[i].volume = 1.0
        heads[i].pan = (i - 2.5) * 0.4
        heads[i].muted = false
        heads[i].reverse = false
        heads[i].filter_lp_hp = 0
        heads[i].filter_bp = 0
        heads[i].filter_q = 0.5
        heads[i].delay = 0
        heads[i].start = 0.0
        heads[i].ending = 1.0
      end
      
      -- E/ Show message
      show_message("Loop Cleared", 2)
      
      grid_redraw()
      redraw()
    end)
  else
    -- Instant clear (no fade)
    loop_exists = false
    loop_length = 0
    recording = false
    
    softcut.rec(1, 0)
    softcut.play(1, 0)
    
    for i = 1, NUM_HEADS do
      softcut.play(heads[i].voice, 0)
      
      -- Reset all head parameters to defaults
      heads[i].pitch = 0
      heads[i].rate = 1.0
      heads[i].volume = 1.0
      heads[i].pan = (i - 2.5) * 0.4
      heads[i].muted = false
      heads[i].reverse = false
      heads[i].filter_lp_hp = 0
      heads[i].filter_bp = 0
      heads[i].filter_q = 0.5
      heads[i].delay = 0
      heads[i].start = 0.0
      heads[i].ending = 1.0
    end
    
    -- E/ Show message
    show_message("Loop Cleared", 2)
    
    grid_redraw()
    redraw()
  end
end

function update_head(head_idx)
  local h = heads[head_idx]
  local v = h.voice
  
  if loop_exists then
    -- Handle mute
    softcut.level(v, h.muted and 0 or h.volume)
    
    -- Pan
    softcut.pan(v, h.pan)
    
    -- Filter system: LP/HP on E2, BP on E3
    -- If BP is active, it takes priority
    if h.filter_bp > 0.1 then
      -- Band-pass filter active
      softcut.post_filter_dry(v, 0.3)
      softcut.post_filter_lp(v, 0)
      softcut.post_filter_hp(v, 0)
      softcut.post_filter_bp(v, h.filter_bp)
      softcut.post_filter_br(v, 0)
      -- BP frequency range: 200Hz to 8kHz
      local freq = util.linexp(0.1, 1, 200, 8000, h.filter_bp)
      softcut.post_filter_fc(v, freq)
      softcut.post_filter_rq(v, h.filter_q)
    elseif h.filter_lp_hp < -0.1 then
      -- High-pass filter (CCW/Left on E2)
      softcut.post_filter_dry(v, 0.3)
      softcut.post_filter_lp(v, 0)
      softcut.post_filter_hp(v, 1.0)
      softcut.post_filter_bp(v, 0)
      softcut.post_filter_br(v, 0)
      -- Map filter value to frequency (lower values = higher cutoff for HP)
      local freq = util.linexp(-1, -0.1, 100, 8000, h.filter_lp_hp)
      softcut.post_filter_fc(v, freq)
      softcut.post_filter_rq(v, h.filter_q)
    elseif h.filter_lp_hp > 0.1 then
      -- Low-pass filter (CW/Right on E2)
      softcut.post_filter_dry(v, 0.3)
      softcut.post_filter_lp(v, 1.0)
      softcut.post_filter_hp(v, 0)
      softcut.post_filter_bp(v, 0)
      softcut.post_filter_br(v, 0)
      -- Map filter value to frequency (higher values = lower cutoff for LP)
      local freq = util.linexp(0.1, 1, 20000, 200, h.filter_lp_hp)
      softcut.post_filter_fc(v, freq)
      softcut.post_filter_rq(v, h.filter_q)
    else
      -- No filter (dead zone is now -0.1 to 0.1)
      softcut.post_filter_dry(v, 1.0)
      softcut.post_filter_lp(v, 0)
      softcut.post_filter_hp(v, 0)
      softcut.post_filter_bp(v, 0)
      softcut.post_filter_br(v, 0)
    end
    
    -- Delay send
    softcut.level_cut_cut(v, 6, h.delay)
    
    -- Calculate rate from pitch and reverse
    h.rate = pitch_to_rate(h.pitch)
    local final_rate = h.reverse and -h.rate or h.rate
    softcut.rate(v, final_rate)
    
    local start_pos = h.start * loop_length
    local end_pos = h.ending * loop_length
    
    if h.ending <= h.start then
      end_pos = (h.start + 0.01) * loop_length
    end
    
    softcut.loop_start(v, start_pos)
    softcut.loop_end(v, end_pos)
  end
end

-- MIDI event handler
function midi_event(data)
  local msg = midi.to_msg(data)
  
  if msg.type == "cc" then
    local param_name = midi_cc_params[msg.cc]
    
    if param_name then
      -- Check if it's a tape parameter
      if param_name == "tape_send_1" or param_name == "tape_send_2" or 
         param_name == "tape_send_3" or param_name == "tape_send_4" then
        -- Handle tape send CC
        local send_num = tonumber(param_name:match("%d+"))
        local normalized = msg.val / 127
        params:set("tape_send_" .. send_num, normalized)
        grid_redraw()
        redraw()
        
      elseif param_name == "tape_volume" then
        -- Handle tape volume CC
        local normalized = msg.val / 127
        params:set("tape_volume", normalized)
        grid_redraw()
        redraw()
        
      else
        -- Handle head parameters
        local h = heads[active_head]
        local param_def = nil
        
        -- Find parameter definition
        for i, p in ipairs(params_list) do
          if p.name == param_name then
            param_def = p
            break
          end
        end
        
        if param_def then
          -- Convert MIDI value (0-127) to parameter range
          local normalized = msg.val / 127
          local min_val, max_val = param_def.min, param_def.max
          
          -- Adjust range for pitch based on mode
          if param_name == "pitch" then
            min_val, max_val = get_pitch_range()
          end
          
          local value = min_val + (normalized * (max_val - min_val))
          
          if param_name == "volume" then
            h.volume = value
          elseif param_name == "pitch" then
            h.pitch = value
          elseif param_name == "pan" then
            h.pan = value
          elseif param_name == "filter_lp_hp" then
            h.filter_lp_hp = value
          elseif param_name == "filter_bp" then
            h.filter_bp = value
          elseif param_name == "filter_q" then
            h.filter_q = value
          elseif param_name == "delay" then
            h.delay = value
          elseif param_name == "start" then
            h.start = util.clamp(value, min_val, h.ending - 0.01)
          elseif param_name == "end" then
            h.ending = util.clamp(value, h.start + 0.01, max_val)
          end
          
          update_head(active_head)
          grid_redraw()
          redraw()
        end
      end
    end
    
  elseif msg.type == "note_on" then
    -- Handle tape control notes
    if msg.note == params:get("note_tape_rec") then
      -- Tape Rec/Stop
      if not tape_recording then
        start_tape_recording()
      else
        if tape_overdubbing then
          stop_tape_overdub()
        else
          stop_tape_recording()
        end
      end
      grid_redraw()
      redraw()
      
    elseif msg.note == params:get("note_tape_overdub") then
      -- Tape Overdub
      if not tape_recording and tape_exists then
        start_tape_overdub()
      elseif tape_overdubbing then
        stop_tape_overdub()
      end
      grid_redraw()
      redraw()
      
    elseif msg.note == params:get("note_tape_clear") then
      -- Tape Clear
      if tape_exists then
        clear_tape()
      end
      grid_redraw()
      redraw()
      
    elseif msg.note == params:get("note_tape_mute") then
      -- Tape Mute toggle
      toggle_tape_mute()
      grid_redraw()
      redraw()
      
    elseif msg.note == params:get("note_tape_reverse") then
      -- Tape Reverse toggle
      toggle_tape_reverse()
      grid_redraw()
      redraw()
    end
  end
end

function key(n, z)
  if n == 2 then
    -- K2 state tracking
    if z == 1 then
      k2_pressed = true
      k2_press_time = util.time()
      
      -- Check if K3 is already pressed (K2+K3 combo)
      if k3_pressed then
        -- K2+K3 combo: Change screen page
        screen_page = screen_page == 1 and 2 or 1
        show_message(screen_page == 1 and "PAGE: MAIN" or "PAGE: TAPE", 1.5)
        redraw()
      end
    else
      -- K2 released
      k2_pressed = false
      
      -- Only change head if K3 wasn't pressed (not a combo)
      if not k3_pressed then
        local press_duration = util.time() - k2_press_time
        if press_duration < 0.5 then
          -- Short press: Change active head
          active_head = (active_head % NUM_HEADS) + 1
          grid_redraw()
          redraw()
        end
      end
      
      k2_press_time = 0
    end
    
  elseif n == 3 then
    -- K3 state tracking
    if z == 1 then
      k3_pressed = true
      k3_press_time = util.time()
      
      -- Check if K2 is already pressed (K2+K3 combo)
      if k2_pressed then
        -- K2+K3 combo: Change screen page
        screen_page = screen_page == 1 and 2 or 1
        show_message(screen_page == 1 and "PAGE: MAIN" or "PAGE: TAPE", 1.5)
        redraw()
      end
    else
      -- K3 released
      k3_pressed = false
      
      -- Only execute K3 actions if K2 wasn't pressed (not a combo)
      if not k2_pressed then
        local press_duration = util.time() - k3_press_time
        
        if press_duration > 0.5 then
          -- Long press behavior depends on screen page
          if screen_page == 1 then
            -- Main page: Clear loop
            if loop_exists then
              clear_loop()
            end
          elseif screen_page == 2 then
            -- Tape page: Clear tape (with fade)
            if tape_exists then
              clear_tape()
            end
          end
        else
          -- Short press behavior depends on screen page
          local time_since_last_click = util.time() - k3_double_click_time
          
          if screen_page == 1 then
            -- Main page: Record/Overdub main loop
            if time_since_last_click < k3_double_click_threshold then
              -- Double click: Overdub on/off
              if loop_exists and not recording then
                start_overdub()
              elseif recording and loop_exists then
                stop_overdub()
              end
              k3_double_click_time = 0
            else
              -- Single click: Record/Stop
              if not loop_exists and not recording then
                start_recording()
              elseif recording and not loop_exists then
                stop_recording()
              end
              
              k3_double_click_time = util.time()
            end
          elseif screen_page == 2 then
            -- Tape page: Record/Overdub tape
            if time_since_last_click < k3_double_click_threshold then
              -- Double click: Tape overdub on/off
              if tape_exists and not tape_recording then
                start_tape_overdub()
              elseif tape_overdubbing then
                stop_tape_overdub()
              end
              k3_double_click_time = 0
            else
              -- Single click: Tape record/stop
              if not tape_exists and not tape_recording and loop_exists then
                start_tape_recording()
              elseif tape_recording and not tape_overdubbing then
                stop_tape_recording()
              end
              
              k3_double_click_time = util.time()
            end
          end
        end
      end
      
      k3_press_time = 0
    end
  end
end

function enc(n, d)
  if screen_page == 1 then
    -- PAGE 1: MAIN (Head control)
    if n == 1 then
      -- E1: Change parameter - each click moves one parameter
      active_param = util.clamp(active_param + d, 1, #params_list)
      redraw()
    else
      local h = heads[active_head]
      local param = params_list[active_param]
      
      if param.name == "volume" then
        local delta = d / (n == 2 and 50 or 200)
        h.volume = util.clamp(h.volume + delta * 2, param.min, param.max)
      elseif param.name == "pitch" then
        -- Get appropriate delta based on pitch mode
        local delta
        if pitch_mode == 2 then
          -- Octaves mode: smaller increments
          delta = d / (n == 2 and 100 or 400)
        else
          -- Semitones mode: whole numbers for E2, decimals for E3
          delta = n == 2 and d or d / 10
        end
        local min_pitch, max_pitch = get_pitch_range()
        h.pitch = util.clamp(h.pitch + delta, min_pitch, max_pitch)
      elseif param.name == "pan" then
        local delta = d / (n == 2 and 50 or 200)
        h.pan = util.clamp(h.pan + delta * 2, param.min, param.max)
      elseif param.name == "filter_lp_hp" then
        -- A/ E2 controls LP (CW/right) and HP (CCW/left)
        if n == 2 then
          local delta = d / 50
          h.filter_lp_hp = util.clamp(h.filter_lp_hp + delta * 2, param.min, param.max)
        end
      elseif param.name == "filter_bp" then
        -- A/ E3 controls BP amount
        if n == 3 then
          local delta = d / 200
          h.filter_bp = util.clamp(h.filter_bp + delta, param.min, param.max)
        end
      elseif param.name == "filter_q" then
        -- E2 and E3 both control resonance
        local delta = d / (n == 2 and 50 or 200)
        h.filter_q = util.clamp(h.filter_q + delta * 3, param.min, param.max)
      elseif param.name == "delay" then
        local delta = d / (n == 2 and 50 or 200)
        h.delay = util.clamp(h.delay + delta, param.min, param.max)
      elseif param.name == "start" then
        local delta = d / (n == 2 and 50 or 200)
        h.start = util.clamp(h.start + delta, param.min, h.ending - 0.01)
      elseif param.name == "end" then
        local delta = d / (n == 2 and 50 or 200)
        h.ending = util.clamp(h.ending + delta, h.start + 0.01, param.max)
      end
      
      update_head(active_head)
      grid_redraw()
      redraw()
    end
    
  elseif screen_page == 2 then
    -- PAGE 2: TAPE RECORDER
    if n == 1 then
      -- E1: Change tape parameter (1-7: send1-4, volume, reverse, mute)
      tape_page_param = util.clamp(tape_page_param + d, 1, 7)
      redraw()
    else
      -- E2/E3: Adjust selected tape parameter
      if tape_page_param >= 1 and tape_page_param <= 4 then
        -- Send levels 1-4
        local send_param = "tape_send_" .. tape_page_param
        local current = params:get(send_param)
        local delta = d / (n == 2 and 50 or 200)
        params:set(send_param, util.clamp(current + delta, 0, 1))
      elseif tape_page_param == 5 then
        -- Tape volume
        local current = params:get("tape_volume")
        local delta = d / (n == 2 and 50 or 200)
        params:set("tape_volume", util.clamp(current + delta, 0, 1))
        update_tape_playback()
      elseif tape_page_param == 6 then
        -- Reverse (toggle on any turn)
        if d ~= 0 then
          toggle_tape_reverse()
        end
      elseif tape_page_param == 7 then
        -- Mute (toggle on any turn)
        if d ~= 0 then
          toggle_tape_mute()
        end
      end
      redraw()
    end
  end
end

function redraw()
  screen.clear()
  
  if screen_page == 1 then
    -- PAGE 1: MAIN (Head control)
    draw_main_page()
  elseif screen_page == 2 then
    -- PAGE 2: TAPE RECORDER
    draw_tape_page()
  end
  
  -- Display message if active with inverted background
  if message_text ~= "" and (util.time() - message_time) < message_duration then
    screen.font_size(12)
    local text_width = screen.text_extents(message_text)
    local text_height = 14
    local padding = 8
    local box_width = text_width + padding * 2
    local box_height = text_height + padding
    local box_x = 64 - box_width / 2
    local box_y = 32 - box_height / 2
    
    -- Draw white background box
    screen.level(15)
    screen.rect(box_x, box_y, box_width, box_height)
    screen.fill()
    
    -- Draw black text on white background
    screen.level(0)
    screen.move(64, 32 + 4)
    screen.text_center(message_text)
    screen.font_size(8)
  end
  
  screen.update()
end

function draw_main_page()
  -- Header
  screen.level(15)
  screen.move(0, 8)
  screen.text("HeadLoop v1.6")
  
  -- Status
  screen.move(128, 8)
  if recording then
    if loop_exists then
      screen.text_right("OVRD")
    else
      -- D/ Show recording time counter
      local rec_elapsed = util.time() - rec_time
      screen.text_right(string.format("REC %.1fs", rec_elapsed))
    end
  else
    screen.text_right(loop_exists and string.format("%.1fs", loop_length) or "---")
  end
  
  -- Active head indicator
  screen.move(0, 20)
  screen.level(8)
  screen.text("Head:")
  screen.level(15)
  screen.move(30, 20)
  screen.text(active_head)
  
  -- Mute/Reverse indicators
  local h = heads[active_head]
  if h.muted then
    screen.level(8)
    screen.move(45, 20)
    screen.text("M")
  end
  if h.reverse then
    screen.level(8)
    screen.move(55, 20)
    screen.text("R")
  end
  
  -- Parameter name
  screen.move(70, 20)
  screen.level(8)
  screen.text(params_list[active_param].name:upper())
  
  -- All heads mini display
  for i = 1, NUM_HEADS do
    local x = (i - 1) * 32
    local y = 28
    
    screen.level(i == active_head and 15 or 4)
    screen.move(x + 2, y)
    screen.text(i)
    
    -- Mute indicator
    if heads[i].muted then
      screen.level(8)
      screen.move(x + 10, y)
      screen.text("M")
    end
    
    -- Position bar
    if loop_exists then
      local bar_w = 28
      local bar_h = 3
      screen.level(i == active_head and 8 or 2)
      screen.rect(x + 2, y + 2, bar_w, bar_h)
      screen.stroke()
      
      screen.level(i == active_head and 15 or 6)
      local pos_x = x + 2 + (heads[i].position * bar_w)
      screen.move(pos_x, y + 2)
      screen.line(pos_x, y + 2 + bar_h)
      screen.stroke()
    end
  end
  
  -- Large parameter value display
  local param = params_list[active_param]
  local value
  local display_text
  
  if param.name == "volume" then
    value = h.volume
    display_text = string.format("%.2f", value)
  elseif param.name == "pitch" then
    value = h.pitch
    -- Show pitch with appropriate unit
    if pitch_mode == 2 then
      display_text = string.format("%+.2foct", value)
    else
      display_text = string.format("%+.1fst", value)
    end
  elseif param.name == "pan" then
    value = h.pan
    if value < -0.01 then
      display_text = string.format("L%.2f", math.abs(value))
    elseif value > 0.01 then
      display_text = string.format("R%.2f", value)
    else
      display_text = "C"
    end
  elseif param.name == "filter_lp_hp" then
    value = h.filter_lp_hp
    if value < -0.1 then
      local freq = util.linexp(-1, -0.1, 100, 8000, value)
      display_text = string.format("HP %.0fHz", freq)
    elseif value > 0.1 then
      local freq = util.linexp(0.1, 1, 20000, 200, value)
      if freq > 1000 then
        display_text = string.format("LP %.1fkHz", freq/1000)
      else
        display_text = string.format("LP %.0fHz", freq)
      end
    else
      display_text = "---"
    end
  elseif param.name == "filter_bp" then
    value = h.filter_bp
    if value > 0.1 then
      local freq = util.linexp(0.1, 1, 200, 8000, value)
      if freq > 1000 then
        display_text = string.format("BP %.1fkHz", freq/1000)
      else
        display_text = string.format("BP %.0fHz", freq)
      end
    else
      display_text = "---"
    end
  elseif param.name == "filter_q" then
    value = h.filter_q
    display_text = string.format("Q %.2f", value)
  elseif param.name == "delay" then
    value = h.delay
    display_text = string.format("%.2f", value)
  elseif param.name == "start" then
    value = h.start
    display_text = string.format("%.2f", value)
  elseif param.name == "end" then
    value = h.ending
    display_text = string.format("%.2f", value)
  end
  
  screen.level(15)
  screen.move(64, 50)
  screen.font_size(16)
  screen.text_center(display_text)
  screen.font_size(8)
  
  -- Value bar (skip for pitch, pan, and filter_lp_hp since they can be negative/centered)
  if param.name ~= "pitch" and param.name ~= "pan" and param.name ~= "filter_lp_hp" then
    local bar_y = 55
    local bar_w = 120
    local bar_h = 4
    local bar_x = 4
    
    screen.level(4)
    screen.rect(bar_x, bar_y, bar_w, bar_h)
    screen.stroke()
    
    local normalized = (value - param.min) / (param.max - param.min)
    screen.level(15)
    screen.rect(bar_x, bar_y, normalized * bar_w, bar_h)
    screen.fill()
  else
    -- Center bar for pitch, pan, and filter_lp_hp
    local bar_y = 55
    local bar_w = 120
    local bar_h = 4
    local bar_x = 4
    local center_x = bar_x + bar_w / 2
    
    screen.level(4)
    screen.rect(bar_x, bar_y, bar_w, bar_h)
    screen.stroke()
    
    -- Center line
    screen.level(8)
    screen.move(center_x, bar_y)
    screen.line(center_x, bar_y + bar_h)
    screen.stroke()
    
    -- Value bar from center
    local normalized
    if param.name == "pitch" then
      local min_pitch, max_pitch = get_pitch_range()
      normalized = value / max_pitch -- Normalize to max range
    else -- pan or filter_lp_hp
      normalized = value -- -1 to +1
    end
    local bar_width = math.abs(normalized) * (bar_w / 2)
    local start_x = normalized < 0 and (center_x - bar_width) or center_x
    
    screen.level(15)
    screen.rect(start_x, bar_y, bar_width, bar_h)
    screen.fill()
  end
end

function draw_tape_page()
  local h = heads[active_head]
  
  -- Header
  screen.level(15)
  screen.move(0, 8)
  screen.text("TAPE RECORDER")
  
  -- Status
  screen.move(128, 8)
  if tape_recording then
    if tape_overdubbing then
      screen.text_right("OVRD")
    else
      local rec_elapsed = util.time() - rec_time
      screen.text_right(string.format("REC %.1fs", rec_elapsed))
    end
  elseif tape_exists then
    screen.text_right(string.format("%.1fs", tape_length_recorded))
  else
    screen.text_right("---")
  end
  
  -- Tape parameters list (left side)
  local param_names = {"Send H1", "Send H2", "Send H3", "Send H4", "Volume", "Reverse", "Mute"}
  
  for i = 1, 7 do
    local y = 16 + (i * 6)
    screen.move(2, y)
    
    if i == tape_page_param then
      screen.level(15)
      screen.text("> " .. param_names[i])
    else
      screen.level(4)
      screen.text("  " .. param_names[i])
    end
  end
  
  -- Current parameter value (right side, moved more to the right and smaller)
  screen.level(15)
  screen.move(92, 32)
  screen.font_size(12)
  
  local display_text
  if tape_page_param >= 1 and tape_page_param <= 4 then
    -- Send levels
    local send_val = params:get("tape_send_" .. tape_page_param)
    display_text = string.format("%.2f", send_val)
  elseif tape_page_param == 5 then
    -- Volume
    local vol = params:get("tape_volume")
    display_text = string.format("%.2f", vol)
  elseif tape_page_param == 6 then
    -- Reverse
    display_text = tape_reverse and "ON" or "OFF"
  elseif tape_page_param == 7 then
    -- Mute
    display_text = tape_muted and "MUTED" or "ON"
  end
  
  screen.text_center(display_text)
  screen.font_size(8)
  
  -- Value bar (for send levels and volume only) - moved right and smaller
  if tape_page_param <= 5 then
    local bar_y = 42
    local bar_w = 48
    local bar_h = 3
    local bar_x = 68
    
    screen.level(4)
    screen.rect(bar_x, bar_y, bar_w, bar_h)
    screen.stroke()
    
    local value
    if tape_page_param <= 4 then
      value = params:get("tape_send_" .. tape_page_param)
    else
      value = params:get("tape_volume")
    end
    
    screen.level(15)
    screen.rect(bar_x, bar_y, value * bar_w, bar_h)
    screen.fill()
  end
  
  -- Tape state indicators (all on right lower part)
  screen.level(8)
  if tape_exists then
    screen.move(128, 60)
    if tape_recording then
      screen.level(15)
      screen.text_right(tape_overdubbing and "OVERDUB" or "RECORDING")
    elseif tape_playing then
      screen.level(15)
      local status = tape_muted and "MUTED" or "PLAYING"
      if tape_reverse and not tape_muted then
        status = status .. " REV"
      end
      screen.text_right(status)
    else
      screen.level(15)
      screen.text_right("STOPPED")
    end
  else
    -- Moved to right lower part of screen
    screen.move(128, 60)
    screen.text_right("EMPTY")
  end
end

function cleanup()
  if tape_clock then
    clock.cancel(tape_clock)
  end
  
  if lfo_clock then
    clock.cancel(lfo_clock)
  end
  
  for i = 1, NUM_HEADS + 2 do -- +2 for recording and delay voices (max 6 voices total)
    softcut.enable(i, 0)
  end
end
