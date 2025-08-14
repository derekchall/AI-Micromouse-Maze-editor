import tkinter as tk
from tkinter import Canvas, messagebox
import json
import math
import random
import time
import os
import sys
import numpy as np
from collections import deque

# --- Sound Engine using Pygame ---
try:
    import pygame
    PYGAME_AVAILABLE = True
except ImportError:
    PYGAME_AVAILABLE = False
    print("WARNING: Pygame library not found. Sound effects will be disabled.")
    print("Install using: pip install pygame")


# --- Game Constants ---
PACMAN_GAME_SPEED_MS = 15      # Target UI update rate
PACMAN_BASE_SPEED_CPS = 2.5    # Base speed in Cells Per Second
GHOST_SPEEDS_CPS = [2.4, 2.3, 2.6, 2.2] # Blinky, Pinky, Inky, Clyde speeds in CPS
PACMAN_MAX_SPEED_MODIFIER = 1.5 # Additional speed increase (150%) when all pellets are eaten

# --- Visual Constants ---
DEFAULT_CELL_VISUAL_SIZE_PX = 25
MARGIN = 25

# --- Directions ---
N4, E4, S4, W4 = 0, 1, 2, 3
DR4 = [-1, 0, 1, 0]; DC4 = [0, 1, 0, -1]

# --- Sound Helper Class ---
class NoSound:
    def play(self, loops=0): pass
    def stop(self): pass
    def set_volume(self, vol): pass
    def get_busy(self): return False

class PacmanGame:
    def __init__(self, master, maze_data):
        self.master = master
        self.master.title("Pac-Man")
        # Start window maximized
        self.master.state('zoomed')
        self.master.protocol("WM_DELETE_WINDOW", self.on_close)
        
        # Load data from JSON
        self.grid_size = maze_data.get('grid_size', 16)
        self.h_walls = maze_data.get('h_walls', [])
        self.v_walls = maze_data.get('v_walls', [])
        self.start_cell = tuple(maze_data.get('start_cell', (self.grid_size - 1, 0)))
        goal_cells_list = maze_data.get('goal_cells', [])
        self.goal_cells = {tuple(cell) for cell in goal_cells_list}
        
        # Initialize cell size, will be calculated on first resize
        self.cell_visual_size_px = DEFAULT_CELL_VISUAL_SIZE_PX

        self.canvas = Canvas(master, bg="black", highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)

        # --- Game State ---
        self.pacman_is_dying = False
        self.pacman_eating_ghost = None
        self.pacman_death_anim_id = None
        self.pacman_game_loop_id = None
        self.pacman_score = 0
        self.pacman_lives = 3
        self.pacman_pos = self.start_cell
        self.pacman_px, self.pacman_py = 0, 0 # Will be set in first resize
        self.pacman_dir = E4
        self.pacman_next_dir = E4
        self.pacman_is_moving = False
        self.global_anim_counter = 0
        self.pacman_pellets = {}
        self.pacman_power_pellets = {}
        self.pacman_cherry = None
        self.pacman_next_cherry_time = 0
        self.pacman_initial_pellet_count = 0
        self.pacman_start_time = 0
        self.ghosts = []
        self.pacman_current_ghost_sound_index = -1
        self.ghost_speed_multiplier = 1.0
        self.pacman_game_over_state = None
        self.frightened_timer = 0
        self.ghost_eaten_bonus = 200
        self.ghost_return_map = None 
        self.pacman_last_loop_time = 0
        
        # Resizing logic
        self.resize_timer = None
        self.master.bind("<Configure>", self.schedule_resize)

        self._init_sound()
        self.start_game()
        
        # Trigger initial resize calculation
        self.master.update()
        self._perform_resize()


    def cell_center_to_pixel(self, r, c):
        x = MARGIN + (c + 0.5) * self.cell_visual_size_px
        y = MARGIN + (r + 0.5) * self.cell_visual_size_px
        return x, y

    def post_to_pixel(self, r_post, c_post):
        x = MARGIN + c_post * self.cell_visual_size_px
        y = MARGIN + r_post * self.cell_visual_size_px
        return x, y

    def has_wall(self, r, c, direction4):
        gs = self.grid_size
        if not (0 <= r < gs and 0 <= c < gs): return True
        try:
            if direction4 == N4: return self.h_walls[r][c]
            elif direction4 == E4: return self.v_walls[r][c+1]
            elif direction4 == S4: return self.h_walls[r+1][c]
            elif direction4 == W4: return self.v_walls[r][c]
        except IndexError: return True
        return False

    def schedule_resize(self, event=None):
        """Debounce the resize event to avoid excessive redrawing."""
        if self.resize_timer:
            self.master.after_cancel(self.resize_timer)
        self.resize_timer = self.master.after(100, self._perform_resize)
        
    def _perform_resize(self):
        """Recalculate sizes and redraw the game."""
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()

        if canvas_width <= 1 or canvas_height <= 1:
            return

        # Calculate cell size based on the smaller dimension to maintain aspect ratio
        height_for_maze = canvas_height - MARGIN * 2 - 40 # Account for margins and lives display
        cell_size_w = (canvas_width - MARGIN * 2) / self.grid_size
        cell_size_h = height_for_maze / self.grid_size
        
        self.cell_visual_size_px = max(5, min(cell_size_w, cell_size_h))

        # Update pixel positions of all dynamic objects
        self._update_pixel_positions()
        
        # Redraw the entire game with the new scale
        self.draw_game()

    def _update_pixel_positions(self):
        """Updates the pixel coordinates of Pac-Man and ghosts based on the current cell size."""
        self.pacman_px, self.pacman_py = self.cell_center_to_pixel(*self.pacman_pos)
        for ghost in self.ghosts:
            ghost['px'], ghost['py'] = self.cell_center_to_pixel(*ghost['pos'])

    def _init_sound(self):
        global PYGAME_AVAILABLE
        script_dir = os.path.dirname(os.path.abspath(__file__))
        
        if PYGAME_AVAILABLE:
            try:
                pygame.mixer.init()
                pygame.mixer.set_num_channels(16)
                
                def get_sound(filename):
                    fpath = os.path.join(script_dir, "sounds", filename)
                    return pygame.mixer.Sound(fpath) if os.path.exists(fpath) else NoSound()

                self.sound_start = get_sound("start.wav")
                self.sound_waka = get_sound("waka.wav")
                self.sound_death = get_sound("death.wav")
                self.sound_power_pellet = get_sound("power_pellet.wav")
                self.sound_eat_ghost = get_sound("eat_ghost.wav")
                self.sound_ghost_eyes = get_sound("ghost_eyes.wav")
                self.sound_eat_fruit = get_sound("eat_fruit.wav")

                self.sound_ghosts = [get_sound(f"ghost{i}.wav") for i in range(1, 6)]
                
                self.ghost_channel = pygame.mixer.Channel(1)
                self.eyes_channel = pygame.mixer.Channel(2)
                self.fruit_channel = pygame.mixer.Channel(3)
            except Exception as e:
                print(f"Pygame mixer init failed: {e}")
                PYGAME_AVAILABLE = False
        
        if not PYGAME_AVAILABLE:
            self.sound_start = self.sound_waka = self.sound_death = NoSound()
            self.sound_power_pellet = self.sound_eat_ghost = self.sound_ghost_eyes = NoSound()
            self.sound_eat_fruit = NoSound()
            self.sound_ghosts = []
            self.ghost_channel = self.eyes_channel = self.fruit_channel = NoSound()

    def _stop_all_sounds(self):
        """Stops all looping sound channels."""
        if not PYGAME_AVAILABLE:
            return
        self.ghost_channel.stop()
        self.eyes_channel.stop()
        self.fruit_channel.stop()

    def start_game(self):
        self.pacman_is_dying = False
        self.pacman_eating_ghost = None
        self.pacman_score = 0
        self.pacman_lives = 3
        self.pacman_pos = self.start_cell
        self.pacman_dir = E4
        self.pacman_next_dir = E4
        self.pacman_is_moving = False
        self.global_anim_counter = 0
        self.ghost_speed_multiplier = 1.0
        self.pacman_game_over_state = None
        self.frightened_timer = 0
        self.pacman_cherry = None
        self.pacman_next_cherry_time = time.time() + random.uniform(10, 15)
        self.pacman_pellets.clear()
        self.ghosts.clear()

        accessible_cells = self._find_accessible_pellets()
        for r, c in accessible_cells:
            if (r, c) not in self.goal_cells:
                self.pacman_pellets[(r, c)] = 0
            
        self._place_power_pellets(accessible_cells)
        self.pacman_initial_pellet_count = len(self.pacman_pellets) + len(self.pacman_power_pellets)
        
        self._create_ghost_return_map()

        gs = self.grid_size
        center = gs // 2
        
        goal_cell_list = list(self.goal_cells) if self.goal_cells else []
        default_starts = [(center-2, center-1), (center-1, center-2), (center-1, center), (center, center-1)]
        ghost_colors = ['#FF0000', '#FFB8FF', '#00FFFF', '#FFB852']
        
        for i in range(4):
            r, c = goal_cell_list[i] if i < len(goal_cell_list) else default_starts[i]
            px, py = self.cell_center_to_pixel(r, c)
            self.ghosts.append({
                'id': i, 'pos': (r, c), 'px': px, 'py': py, 'color': ghost_colors[i],
                'dir': N4, 'state': 'waiting', 'release_time': i * 3.0,
                'speed': GHOST_SPEEDS_CPS[i], 'is_moving': False, 'reversal_pending': False
            })
        
        self.pacman_start_time = 0
        self.sound_start.play() # Play intro sound only ONCE here
        
        self._bind_pacman_keys()
        self.canvas.focus_set()
        
        self.draw_game()
        self.pacman_game_loop_id = self.master.after(4000, self._start_pacman_gameplay)

    def on_close(self):
        if self.pacman_game_loop_id: self.master.after_cancel(self.pacman_game_loop_id)
        if self.pacman_death_anim_id: self.master.after_cancel(self.pacman_death_anim_id)
        self.pacman_game_loop_id = None
        self.pacman_death_anim_id = None
        if PYGAME_AVAILABLE:
            pygame.mixer.quit()
        self.master.destroy()

    def _create_ghost_return_map(self):
        gs = self.grid_size
        self.ghost_return_map = np.full((gs, gs), float('inf'))
        q = deque()

        if not self.goal_cells:
            center = (gs // 2 -1, gs // 2 -1)
            self.goal_cells.add(center)

        for r_goal, c_goal in self.goal_cells:
            if 0 <= r_goal < gs and 0 <= c_goal < gs:
                self.ghost_return_map[r_goal, c_goal] = 0
                q.append((r_goal, c_goal))
        
        while q:
            r, c = q.popleft()
            current_dist = self.ghost_return_map[r, c]
            for dir4 in range(4):
                if not self.has_wall(r, c, dir4):
                    nr, nc = r + DR4[dir4], c + DC4[dir4]
                    if 0 <= nr < gs and 0 <= nc < gs and self.ghost_return_map[nr, nc] == float('inf'):
                        self.ghost_return_map[nr, nc] = current_dist + 1
                        q.append((nr, nc))

    def _find_accessible_pellets(self):
        q = deque([self.start_cell])
        visited = {self.start_cell}
        gs = self.grid_size
        while q:
            r, c = q.popleft()
            for dir4 in range(4):
                if not self.has_wall(r, c, dir4):
                    nr, nc = r + DR4[dir4], c + DC4[dir4]
                    if (0 <= nr < gs and 0 <= nc < gs and (nr, nc) not in visited):
                        visited.add((nr, nc))
                        q.append((nr, nc))
        return visited

    def _place_power_pellets(self, accessible_cells):
        self.pacman_power_pellets.clear()
        gs = self.grid_size
        corners = [(1, 1), (1, gs - 2), (gs - 2, 1), (gs - 2, gs - 2)]
        
        for r_start, c_start in corners:
            placed = False
            for r_offset in range(gs // 4):
                for c_offset in range(gs // 4):
                    r_check = r_start + r_offset if r_start < gs / 2 else r_start - r_offset
                    c_check = c_start + c_offset if c_start < gs / 2 else c_start - c_offset
                    
                    if (r_check, c_check) in accessible_cells and (r_check, c_check) not in self.goal_cells:
                        self.pacman_power_pellets[(r_check, c_check)] = 0
                        placed = True
                        break
                if placed: break
        
        for pos in self.pacman_power_pellets:
            if pos in self.pacman_pellets:
                del self.pacman_pellets[pos]

    def _start_ghost_siren(self):
        """Correctly starts or changes the ghost siren sound."""
        if not PYGAME_AVAILABLE or self.pacman_is_dying or self.frightened_timer > 0:
            return

        pellets_eaten = self.pacman_initial_pellet_count - (len(self.pacman_pellets) + len(self.pacman_power_pellets))
        percent_eaten = pellets_eaten / self.pacman_initial_pellet_count if self.pacman_initial_pellet_count > 0 else 0
        num_sounds = len(self.sound_ghosts)
        
        target_sound_index = 0
        if num_sounds > 0:
            target_sound_index = min(int(percent_eaten * num_sounds), num_sounds - 1)

        # Condition to start the sound if it's not playing, or change it if the index is wrong.
        if self.pacman_current_ghost_sound_index != target_sound_index or not self.ghost_channel.get_busy():
            # Only update ghost behavior if the sound level actually changes during gameplay
            if self.pacman_current_ghost_sound_index != target_sound_index and self.pacman_current_ghost_sound_index != -1:
                self.ghost_speed_multiplier *= 1.05
                for g in self.ghosts:
                    if g['state'] == 'active':
                        g['reversal_pending'] = True
            
            self.pacman_current_ghost_sound_index = target_sound_index
            if self.sound_ghosts:
                self.ghost_channel.play(self.sound_ghosts[self.pacman_current_ghost_sound_index], loops=-1)

    def _bind_pacman_keys(self):
        self.master.bind("<KeyPress-Up>", lambda e: self._on_pacman_key_press(N4))
        self.master.bind("<KeyPress-Down>", lambda e: self._on_pacman_key_press(S4))
        self.master.bind("<KeyPress-Left>", lambda e: self._on_pacman_key_press(W4))
        self.master.bind("<KeyPress-Right>", lambda e: self._on_pacman_key_press(E4))

    def _on_pacman_key_press(self, direction):
        if self.pacman_is_dying or self.pacman_eating_ghost: return
        self.pacman_next_dir = direction

    def _pacman_death_animation(self, start_time=None):
        if start_time is None: start_time = time.time()
        
        DEATH_ANIM_DURATION = 2.0
        elapsed = time.time() - start_time
        
        self.canvas.delete("pacman", "pacman_death_pop")

        if elapsed < DEATH_ANIM_DURATION:
            progress = elapsed / (DEATH_ANIM_DURATION * 0.75)
            size = self.cell_visual_size_px * 0.4
            angle = 180 * progress
            extent = 359.9 - (angle * 2)
            if extent > 0:
                self.canvas.create_arc(self.pacman_px - size, self.pacman_py - size, self.pacman_px + size, self.pacman_py + size,
                                   start=angle, extent=extent, fill="yellow", outline="", tags="pacman")
            self.pacman_death_anim_id = self.master.after(15, self._pacman_death_animation, start_time)
        else:
            self.pacman_lives -= 1
            if self.pacman_lives <= 0:
                self._stop_all_sounds()
                self.pacman_game_over_state = 'lose'
                self.draw_game()
                self.master.after(3000, self.on_close)
            else:
                # Reset Pac-Man
                self.pacman_is_dying = False
                self.pacman_pos = self.start_cell
                self.pacman_px, self.pacman_py = self.cell_center_to_pixel(*self.pacman_pos)
                self.pacman_dir = E4
                self.pacman_next_dir = E4
                self.pacman_is_moving = False
                
                # --- GHOST RESET LOGIC ---
                goal_cell_list = list(self.goal_cells) if self.goal_cells else []
                gs = self.grid_size
                center = gs // 2
                default_starts = [(center - 2, center - 1), (center - 1, center - 2), (center-1, center), (center, center-1)]
                
                for i, g in enumerate(self.ghosts):
                    r, c = goal_cell_list[i] if i < len(goal_cell_list) else default_starts[i]
                    g['pos'] = (r, c)
                    g['px'], g['py'] = self.cell_center_to_pixel(*g['pos'])
                    g['state'] = 'waiting'
                    g['is_moving'] = False
                    g['release_time'] = i * 3.0 # Reset release timer
                
                # Reset game timers and restart gameplay after a delay
                self.pacman_start_time = 0
                self.draw_game()
                # DO NOT play intro sound again
                self.pacman_game_loop_id = self.master.after(4000, self._start_pacman_gameplay)

    def _get_ghost_next_direction(self, ghost):
        gr, gc = ghost['pos']
        pac_r, pac_c = self.pacman_pos
        
        if ghost['state'] == 'eaten':
            current_dist = self.ghost_return_map[gr, gc]
            best_dir = ghost['dir']
            for d in [N4, W4, S4, E4]:
                if not self.has_wall(gr, gc, d):
                    nr, nc = gr + DR4[d], gc + DC4[d]
                    if self.ghost_return_map[nr, nc] < current_dist: return d
            return best_dir
        elif ghost['state'] == 'frightened':
            valid_moves = [d for d in range(4) if not self.has_wall(gr, gc, d)]
            opposite_dir = (ghost['dir'] + 2) % 4
            if len(valid_moves) > 1 and opposite_dir in valid_moves:
                valid_moves.remove(opposite_dir)
            return random.choice(valid_moves) if valid_moves else opposite_dir
        else:
            target_tile = None
            pac_dir = self.pacman_dir
            if ghost['id'] == 0: target_tile = (pac_r, pac_c)
            elif ghost['id'] == 1:
                target_tile = (pac_r + 4 * DR4[pac_dir], pac_c + 4 * DC4[pac_dir])
                if pac_dir == N4: target_tile = (target_tile[0], target_tile[1] - 4)
            elif ghost['id'] == 2:
                try:
                    blinky = next(g for g in self.ghosts if g['id'] == 0)
                    br, bc = blinky['pos']
                    ar, ac = (pac_r + 2 * DR4[pac_dir], pac_c + 2 * DC4[pac_dir])
                    target_tile = (ar + (ar - br), ac + (ac - bc))
                except (StopIteration, KeyError): target_tile = (pac_r, pac_c)
            elif ghost['id'] == 3:
                dist_sq = (gr - pac_r)**2 + (gc - pac_c)**2
                if dist_sq > 64: target_tile = (pac_r, pac_c)
                else: target_tile = (self.grid_size - 1, 0)

            best_dir, min_dist_sq = -1, float('inf')
            valid_moves = [d for d in range(4) if not self.has_wall(gr, gc, d)]
            opposite_dir = (ghost['dir'] + 2) % 4
            if len(valid_moves) > 1 and opposite_dir in valid_moves:
                valid_moves.remove(opposite_dir)
            
            for d in [N4, W4, S4, E4]:
                if d in valid_moves:
                    nr, nc = gr + DR4[d], gc + DC4[d]
                    dist_sq = (target_tile[0] - nr)**2 + (target_tile[1] - nc)**2
                    if dist_sq < min_dist_sq: min_dist_sq, best_dir = dist_sq, d
            return best_dir if best_dir != -1 else opposite_dir

    def _start_pacman_gameplay(self):
        self.pacman_current_ghost_sound_index = -1
        self._start_ghost_siren()
        self.pacman_last_loop_time = time.time()
        self._pacman_game_loop()
    
    def _pacman_game_loop(self):
        if self.pacman_is_dying: return

        current_time = time.time()
        delta_t = current_time - self.pacman_last_loop_time
        self.pacman_last_loop_time = current_time
        if delta_t > 0.1: delta_t = 0.1
        
        if self.pacman_eating_ghost:
            self.draw_game()
            self.pacman_game_loop_id = self.master.after(PACMAN_GAME_SPEED_MS, self._pacman_game_loop)
            return

        if self.pacman_start_time == 0: self.pacman_start_time = time.time()
        self.global_anim_counter = (self.global_anim_counter + 1) % 8

        if not self.pacman_is_moving:
            r, c = self.pacman_pos
            if self.pacman_pos in self.pacman_pellets:
                self.pacman_pellets.pop(self.pacman_pos); self.pacman_score += 10; self.sound_waka.play()
            if self.pacman_pos in self.pacman_power_pellets:
                self.pacman_power_pellets.pop(self.pacman_pos); self.pacman_score += 50; self.frightened_timer = 8.0; self.ghost_eaten_bonus = 200
                self.ghost_channel.stop(); self.ghost_channel.play(self.sound_power_pellet, loops=-1)
                for g in self.ghosts:
                    if g['state'] in ['active', 'frightened']: g['state'] = 'frightened'; g['reversal_pending'] = True
            if self.pacman_cherry and self.pacman_pos == self.pacman_cherry['pos']:
                self.pacman_score += 100; self.fruit_channel.play(self.sound_eat_fruit); self.pacman_cherry = None
                self.pacman_next_cherry_time = time.time() + random.uniform(10, 15)
            if not self.pacman_pellets and not self.pacman_power_pellets:
                self._stop_all_sounds()
                self.pacman_game_over_state = 'win'; self.draw_game(); self.master.after(3000, self.on_close); return
            if self.pacman_dir != self.pacman_next_dir and not self.has_wall(r, c, self.pacman_next_dir):
                self.pacman_dir = self.pacman_next_dir
            if not self.has_wall(r, c, self.pacman_dir): self.pacman_is_moving = True
        
        if self.pacman_is_moving:
            pellets_eaten = self.pacman_initial_pellet_count - (len(self.pacman_pellets) + len(self.pacman_power_pellets))
            percent_eaten = pellets_eaten / self.pacman_initial_pellet_count if self.pacman_initial_pellet_count > 0 else 0
            speed_modifier = 1.0 + (percent_eaten**0.7 * PACMAN_MAX_SPEED_MODIFIER)
            effective_speed_cps = PACMAN_BASE_SPEED_CPS * speed_modifier
            move_distance = effective_speed_cps * self.cell_visual_size_px * delta_t
            self.pacman_px += DC4[self.pacman_dir] * move_distance; self.pacman_py += DR4[self.pacman_dir] * move_distance
            next_r, next_c = self.pacman_pos[0] + DR4[self.pacman_dir], self.pacman_pos[1] + DC4[self.pacman_dir]
            center_x, center_y = self.cell_center_to_pixel(next_r, next_c)
            if ((self.pacman_dir == E4 and self.pacman_px >= center_x) or (self.pacman_dir == W4 and self.pacman_px <= center_x) or
                (self.pacman_dir == S4 and self.pacman_py >= center_y) or (self.pacman_dir == N4 and self.pacman_py <= center_y)):
                self.pacman_is_moving = False; self.pacman_pos = (next_r, next_c); self.pacman_px, self.pacman_py = center_x, center_y

        elapsed_time = time.time() - self.pacman_start_time
        for ghost in self.ghosts:
            if ghost['state'] == 'waiting' and elapsed_time >= ghost['release_time']:
                ghost['state'] = 'active'; ghost['is_moving'] = True
            if not ghost['is_moving'] and ghost['state'] != 'waiting':
                gr, gc = ghost['pos']
                if ghost.get('reversal_pending', False):
                    opposite_dir = (ghost['dir'] + 2) % 4
                    if not self.has_wall(gr, gc, opposite_dir): ghost['dir'] = opposite_dir
                    else: ghost['dir'] = self._get_ghost_next_direction(ghost)
                    ghost['reversal_pending'] = False
                else:
                    if ghost['state'] == 'eaten' and ghost['pos'] in self.goal_cells: ghost['state'] = 'active'
                    ghost['dir'] = self._get_ghost_next_direction(ghost)
                if not self.has_wall(gr, gc, ghost['dir']): ghost['is_moving'] = True
            if ghost['is_moving']:
                current_ghost_speed_cps = ghost['speed']
                if ghost['state'] == 'frightened': current_ghost_speed_cps *= 0.8
                elif ghost['state'] == 'eaten': current_ghost_speed_cps *= 2.0
                else: current_ghost_speed_cps *= self.ghost_speed_multiplier
                ghost_move_distance = current_ghost_speed_cps * self.cell_visual_size_px * delta_t
                ghost['px'] += DC4[ghost['dir']] * ghost_move_distance; ghost['py'] += DR4[ghost['dir']] * ghost_move_distance
                next_r, next_c = ghost['pos'][0] + DR4[ghost['dir']], ghost['pos'][1] + DC4[ghost['dir']]
                g_center_x, g_center_y = self.cell_center_to_pixel(next_r, next_c)
                dist_sq = (ghost['px'] - g_center_x)**2 + (ghost['py'] - g_center_y)**2
                if dist_sq <= (ghost_move_distance)**2:
                    ghost['is_moving'] = False; ghost['pos'] = (next_r, next_c); ghost['px'], ghost['py'] = g_center_x, g_center_y

        if self.frightened_timer > 0:
            self.frightened_timer -= delta_t
            if self.frightened_timer <= 0:
                self.ghost_eaten_bonus = 200; self.ghost_channel.stop(); self._start_ghost_siren()
                for ghost in self.ghosts:
                    if ghost['state'] == 'frightened': ghost['state'] = 'active'
        else: self._start_ghost_siren()
        
        for ghost in self.ghosts:
            if ghost['state'] in ['active', 'frightened']:
                if (self.pacman_px - ghost['px'])**2 + (self.pacman_py - ghost['py'])**2 < (self.cell_visual_size_px * 0.2)**2:
                    if ghost['state'] == 'frightened':
                        ghost['state'] = 'eaten'; self.pacman_score += self.ghost_eaten_bonus; self.sound_eat_ghost.play()
                        self.pacman_eating_ghost = {'score': self.ghost_eaten_bonus, 'ghost_id': ghost['id'], 'px': self.pacman_px, 'py': self.pacman_py}
                        self.ghost_eaten_bonus *= 2; self.master.after(1000, lambda: setattr(self, 'pacman_eating_ghost', None))
                    else:
                        self.pacman_is_dying = True; self.ghost_channel.stop(); self.eyes_channel.stop(); self.canvas.delete("ghost"); self.sound_death.play()
                        self._pacman_death_animation(); return
        
        any_eyes_returning = any(g['state'] == 'eaten' for g in self.ghosts)
        if self.eyes_channel.get_busy():
            if any_eyes_returning and not self.eyes_channel.get_busy(): self.eyes_channel.play(self.sound_ghost_eyes, loops=-1)
            elif not any_eyes_returning and self.eyes_channel.get_busy(): self.eyes_channel.stop()
        
        if self.pacman_cherry:
            if time.time() >= self.pacman_cherry['despawn_time']:
                self.pacman_cherry = None; self.pacman_next_cherry_time = time.time() + random.uniform(14, 18)
        elif time.time() >= self.pacman_next_cherry_time:
            self.pacman_cherry = {'pos': self.start_cell, 'despawn_time': time.time() + random.uniform(9, 12)}

        self.draw_game()
        self.pacman_game_loop_id = self.master.after(PACMAN_GAME_SPEED_MS, self._pacman_game_loop)

    def draw_game(self):
        self.canvas.delete("all")
        gs = self.grid_size
        wall_thickness = max(1, self.cell_visual_size_px * 0.05)
        size = self.cell_visual_size_px * 0.35

        # Draw Walls
        for r_wall in range(gs + 1):
            for c_wall in range(gs):
                if self.h_walls[r_wall][c_wall]:
                    x0, y0 = self.post_to_pixel(r_wall, c_wall); x1, _ = self.post_to_pixel(r_wall, c_wall + 1)
                    self.canvas.create_line(x0, y0, x1, y0, fill="#0000FF", width=wall_thickness, tags="wall")
        for r_wall in range(gs):
            for c_wall in range(gs + 1):
                if self.v_walls[r_wall][c_wall]:
                    x0, y0 = self.post_to_pixel(r_wall, c_wall); _, y1 = self.post_to_pixel(r_wall + 1, c_wall)
                    self.canvas.create_line(x0, y0, x0, y1, fill="#0000FF", width=wall_thickness, tags="wall")

        # Draw Pellets
        pellet_size = self.cell_visual_size_px * 0.1
        for (r, c) in self.pacman_pellets.keys():
            x, y = self.cell_center_to_pixel(r, c)
            self.canvas.create_oval(x - pellet_size, y - pellet_size, x + pellet_size, y + pellet_size, fill="white", outline="", tags="pellet")
        
        power_pellet_size = self.cell_visual_size_px * 0.3
        for(r, c) in self.pacman_power_pellets.keys():
            x, y = self.cell_center_to_pixel(r, c)
            self.canvas.create_oval(x - power_pellet_size, y - power_pellet_size, x + power_pellet_size, y + power_pellet_size, fill="orange", outline="", tags="pellet")

        # Draw Cherry
        if self.pacman_cherry:
            r, c = self.pacman_cherry['pos']
            x, y = self.cell_center_to_pixel(r,c)
            radius = self.cell_visual_size_px * 0.15
            self.canvas.create_oval(x - radius, y - radius, x + radius, y + radius, fill='red', outline='darkred', tags='pacman_fruit')
            self.canvas.create_oval(x, y - radius, x + (radius*2), y + radius, fill='red', outline='darkred', tags='pacman_fruit')
            self.canvas.create_line(x+radius, y-radius, x+radius, y - size*0.8, fill='green', width=max(1, wall_thickness), tags='pacman_fruit')

        # Draw Game Characters
        if not self.pacman_game_over_state:
            if not self.pacman_is_dying:
                for ghost in self.ghosts:
                    if self.pacman_eating_ghost and self.pacman_eating_ghost['ghost_id'] == ghost['id']: continue
                    self._draw_ghost(self.canvas, ghost)
            
            if not self.pacman_is_dying and not self.pacman_eating_ghost:
                x, y = self.pacman_px, self.pacman_py
                angle_map = {E4: 45, N4: 135, W4: 225, S4: 315}
                start_angle = angle_map.get(self.pacman_dir, 45)
                is_open = (self.global_anim_counter % 8) < 4
                extent = 270 if (is_open and self.pacman_is_moving) else 359.9
                self.canvas.create_arc(x - size, y - size, x + size, y + size, start=start_angle, extent=extent, fill="yellow", outline="", tags="pacman")
                               
            if self.pacman_eating_ghost:
                info = self.pacman_eating_ghost
                font_size = max(8, int(self.cell_visual_size_px * 0.4))
                self.canvas.create_text(info['px'], info['py'], text=str(info['score']), fill="cyan", font=("Arial", font_size, "bold"), tags="ghost_score")

        # Draw UI (Score, Lives)
        font_size_ui = max(8, int(self.cell_visual_size_px * 0.5))
        score_text = f"SCORE: {self.pacman_score}"
        self.canvas.create_text(MARGIN, MARGIN / 2, text=score_text, anchor='w', fill="white", font=("Arial", font_size_ui, "bold"))
        
        # Position lives at the bottom of the canvas
        lives_y = self.canvas.winfo_height() - MARGIN
        for i in range(self.pacman_lives):
            live_x = MARGIN + i * (size * 2.5)
            self.canvas.create_arc(live_x - size, lives_y - size, live_x + size, lives_y + size, start=45, extent=270, fill="yellow", outline="")
        
        # Draw Game Over / Win Message
        if self.pacman_game_over_state:
            cx = self.canvas.winfo_width() / 2
            cy = self.canvas.winfo_height() / 2
            font_size_end = max(16, int(self.cell_visual_size_px * 1.5))
            
            rect_w, rect_h = font_size_end * 8, font_size_end * 2.5
            self.canvas.create_rectangle(cx - rect_w/2, cy - rect_h/2, cx + rect_w/2, cy + rect_h/2, 
                                         fill="black", outline="yellow", width=2, tags="game_over_text")
            
            if self.pacman_game_over_state == 'win':
                self.canvas.create_text(cx, cy, text="YOU WIN!", fill="yellow", 
                                        font=("Arial", font_size_end, "bold"), tags="game_over_text")
            elif self.pacman_game_over_state == 'lose':
                self.canvas.create_text(cx, cy, text="GAME OVER", fill="red", 
                                        font=("Arial", font_size_end, "bold"), tags="game_over_text")

    def _draw_ghost(self, canvas, ghost):
        x, y, color, direction, state = ghost['px'], ghost['py'], ghost['color'], ghost['dir'], ghost['state']
        size = self.cell_visual_size_px * 0.35
        
        if size < 2: return # Don't draw if too small

        body_color = color
        if state == 'frightened':
            body_color = '#00008B'
            if self.frightened_timer < 3 and (self.global_anim_counter // 2) < 2: body_color = 'white'
        
        if state != 'eaten':
            canvas.create_arc(x-size, y-size, x+size, y+size, start=0, extent=180, fill=body_color, outline="", tags="ghost")
            canvas.create_rectangle(x-size, y, x+size, y+size*0.8, fill=body_color, outline="", tags="ghost")

            bottom_y = y + size * 0.8
            if (self.global_anim_counter // 2) < 2:
                scallop_radius = size / 3
                for i in range(3):
                    scallop_x = (x - size) + (i+0.5) * (size*2/3)
                    canvas.create_oval(scallop_x-scallop_radius, bottom_y-scallop_radius,
                                        scallop_x+scallop_radius, bottom_y+scallop_radius,
                                        fill=body_color, outline="", tags="ghost")
            else:
                leg_height = size * 0.5
                p1,p2,p3,p4,p5 = (x-size,bottom_y),(x-size/2,bottom_y+leg_height),(x,bottom_y),(x+size/2,bottom_y+leg_height),(x+size,bottom_y)
                canvas.create_polygon(p1, p2, p3, fill=body_color, outline="", tags="ghost")
                canvas.create_polygon(p3, p4, p5, fill=body_color, outline="", tags="ghost")

        eye_w, eye_h = max(1, size*0.4), max(1, size*0.5)
        pupil_size = max(1, eye_w * 0.5)
        eye_y = y - size*0.1
        eye_x1 = x - size*0.4
        eye_x2 = x + size*0.4
        
        canvas.create_oval(eye_x1-eye_w/2, eye_y-eye_h/2, eye_x1+eye_w/2, eye_y+eye_h/2, fill='white', outline='black', tags="ghost")
        canvas.create_oval(eye_x2-eye_w/2, eye_y-eye_h/2, eye_x2+eye_w/2, eye_y+eye_h/2, fill='white', outline='black', tags="ghost")
        
        pupil_dx, pupil_dy = {E4: size*0.08, W4: -size*0.08}.get(direction, 0), {N4: -size*0.08, S4: size*0.08}.get(direction, 0)

        canvas.create_oval(eye_x1-pupil_size/2+pupil_dx, eye_y-pupil_size/2+pupil_dy, eye_x1+pupil_size/2+pupil_dx, eye_y+pupil_size/2+pupil_dy, fill='blue', outline='', tags="ghost")
        canvas.create_oval(eye_x2-pupil_size/2+pupil_dx, eye_y-pupil_size/2+pupil_dy, eye_x2+pupil_size/2+pupil_dx, eye_y+pupil_size/2+pupil_dy, fill='blue', outline='', tags="ghost")


if __name__ == "__main__":
    json_file_path = "maze_pacman_data.json"

    if not os.path.exists(json_file_path):
        root = tk.Tk()
        root.withdraw() 
        messagebox.showerror("File Not Found", f"Error: Maze data file not found: '{json_file_path}'\n\nPlease launch from the Maze Editor first.")
        sys.exit(1)

    try:
        with open(json_file_path, 'r') as f:
            maze_data = json.load(f)
    except (json.JSONDecodeError, IOError) as e:
        root = tk.Tk()
        root.withdraw()
        messagebox.showerror("File Error", f"Error reading or parsing maze data file: {e}")
        sys.exit(1)

    root = tk.Tk()
    if not PYGAME_AVAILABLE:
        messagebox.showwarning("Dependency Missing", "Pygame library not found.\nSound effects will be disabled.\n\nInstall using:\npip install pygame", parent=root)
    app = PacmanGame(root, maze_data)
    root.mainloop()