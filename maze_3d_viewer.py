import json
from ursina import *
import os # Import the os library
import sys # Import sys to allow exiting theprogram
from collections import deque # Import deque for the flood fill queue
import math # Import math for angle calculations

# Get the directory where this script is located
script_dir = os.path.dirname(os.path.abspath(__file__))
# Create a full, absolute path to the JSON file
JSON_FILE_PATH = os.path.join(script_dir, 'maze_3d_data.json')

# Globals for maze and UI state
h_walls_data, v_walls_data, goal_cells_data = [], [], []
goal_cells_set = set()
start_cell_data = [0, 0]
grid_size_data = 16
minimap, map_pivot, map_content, minimap_walls = None, None, None, None
seen_cells = set()
free_fly_camera = None
floor_ref = None # Will hold reference to the floor collider

# Globals for solver state
is_solving = False
solve_actions = []
action_in_progress = False
target_position = None
target_rotation = None
initial_target_pos = None
turn_direction = 0
is_decelerating = False

# Globals for manual control
velocity = Vec3(0,0,0)
turn_speed = 125
acceleration = 20
friction = 2.0
gravity = 1
is_chase_cam = False
robot_height = 0.25
zoom_level = 0 # Will be initialized later

# Physics parameters for solver
solve_velocity = 0.0
solve_rotation_velocity = 0.0
solve_acceleration = 20.0
solve_rotation_acceleration = 650.0
max_solve_speed = 200.0
max_solve_rotation_speed = 600.0

CELL_SIZE = 1.8

def dot(v1, v2):
    return v1.x*v2.x + v1.y*v2.y + v1.z*v2.z

class CustomWall(Entity):
    def __init__(self, position=(0, 0, 0), scale=(1, 1, 1), main_texture=None, top_texture=None, **kwargs):
        super().__init__(position=position, scale=scale, collider='box')
        Entity(parent=self, model='cube', texture=main_texture, color=color.white, scale=(1, 0.98, 1), position=(0, -0.01, 0))
        Entity(parent=self, model='cube', texture=top_texture, color=color.red, scale=(1, 0.02, 1), position=(0, 0.49, 0))

class CustomPost(Entity):
    def __init__(self, position=(0, 0, 0), scale=(1, 1, 1), texture=None, is_cheese_post=False, cheese_texture=None, **kwargs):
        post_color = color.white if texture else color.yellow
        super().__init__(model='cube', texture=texture, color=post_color, position=position, scale=scale, collider='box', **kwargs)
        if is_cheese_post:
            bbl=Vec3(-0.5,-0.5,-0.5);bbr=Vec3(0.5,-0.5,-0.5);tbl=Vec3(-0.5,0.5,-0.5);bfl=Vec3(-0.5,-0.5,0.5);bfr=Vec3(0.5,-0.5,0.5);tfl=Vec3(-0.5,0.5,0.5)
            vertices=[bbl,bbr,tbl, bfl,tfl,bfr, bbl,bfl,bfr,bbr, bbl,tbl,tfl,bfl, bbr,bfr,tfl,tbl]
            uvs=[Vec2(0,0),Vec2(1,0),Vec2(0,1), Vec2(0,0),Vec2(0,1),Vec2(1,0), Vec2(0,0),Vec2(0,1),Vec2(1,1),Vec2(1,0), Vec2(0,0),Vec2(1,0),Vec2(1,1),Vec2(0,1), Vec2(0,0),Vec2(1,0),Vec2(1,1),Vec2(0,1)]
            tris=[0,1,2, 3,4,5, 6,7,8,6,8,9, 10,11,12,10,12,13, 14,15,16,14,16,17]
            cheese_wedge_model=Mesh(vertices=vertices,triangles=tris,uvs=uvs,mode='triangle'); cheese_wedge_model.generate_normals()
            desired_world_scale=Vec3(0.6,0.5,0.8); parent_world_scale=scale
            cheese_local_scale=(desired_world_scale.x/parent_world_scale[0],desired_world_scale.y/parent_world_scale[1],desired_world_scale.z/parent_world_scale[2])
            self.cheese=Entity(parent=self,model=cheese_wedge_model,texture=cheese_texture,color=color.white if cheese_texture else color.gold,y=0.5+(cheese_local_scale[1]*0.5),scale=cheese_local_scale,rotation=(0,-90,0))

def create_maze_from_json(JSON_FILE_PATH, textures):
    global h_walls_data,v_walls_data,goal_cells_data,goal_cells_set,start_cell_data,grid_size_data,CELL_SIZE
    try:
        with open(JSON_FILE_PATH, 'r') as f: maze_data = json.load(f)
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"FATAL ERROR: Could not load or parse '{JSON_FILE_PATH}'."); print(f"Details: {e}"); return None, None
    grid_size_data=maze_data.get("grid_size",16);h_walls_data=maze_data.get("h_walls",[]);v_walls_data=maze_data.get("v_walls",[])
    goal_cells_data=maze_data.get("goal_cells",[]);start_cell_data=maze_data.get("start_cell",[0,0]);goal_cells_set={tuple(cell) for cell in goal_cells_data}
    WALL_HEIGHT=0.5;WALL_THICKNESS=0.12;POST_DIAMETER=0.12
    offset_x=(grid_size_data*CELL_SIZE)/2;offset_z=(grid_size_data*CELL_SIZE)/2
    floor_collider=Entity(model='plane',scale=(grid_size_data*CELL_SIZE,1,grid_size_data*CELL_SIZE),collider='box',visible=False)
    for y_cell in range(grid_size_data):
        for x_cell in range(grid_size_data):
            is_goal=(y_cell,x_cell) in goal_cells_set
            tex=textures.get('goal_floor') if is_goal and textures.get('goal_floor') else textures.get('floor')
            pos_x=(x_cell+0.5)*CELL_SIZE-offset_x;pos_z=(grid_size_data-(y_cell+0.5))*CELL_SIZE-offset_z
            Entity(model='plane',scale=CELL_SIZE,position=(pos_x,0.01,pos_z),texture=tex,texture_scale=(1,1))
    wall_length=CELL_SIZE-POST_DIAMETER
    for y,row in enumerate(h_walls_data):
        for x,wall_exists in enumerate(row):
            if wall_exists: CustomWall(position=(x*CELL_SIZE-offset_x+CELL_SIZE/2,WALL_HEIGHT/2,(grid_size_data-y)*CELL_SIZE-offset_z),scale=(wall_length,WALL_HEIGHT,WALL_THICKNESS),main_texture=textures.get('wall'),top_texture=textures.get('wall_top'))
    for y,row in enumerate(v_walls_data):
        for x,wall_exists in enumerate(row):
            if wall_exists: CustomWall(position=(x*CELL_SIZE-offset_x,WALL_HEIGHT/2,((grid_size_data-1-y)*CELL_SIZE-offset_z)+CELL_SIZE/2),scale=(WALL_THICKNESS,WALL_HEIGHT,wall_length),main_texture=textures.get('wall'),top_texture=textures.get('wall_top'))
    special_post_created=False;target_posts_coords=set()
    if goal_cells_data:
        min_x=min(c[1] for c in goal_cells_data);max_x=max(c[1] for c in goal_cells_data);min_y=min(c[0] for c in goal_cells_data);max_y=max(c[0] for c in goal_cells_data)
        for x in range(min_x,max_x+2):
            for y in range(min_y,max_y+2): target_posts_coords.add((x,y))
    for y in range(grid_size_data+1):
        for x in range(grid_size_data+1):
            is_special_post=False;post_height=WALL_HEIGHT
            if not special_post_created and (x,y) in target_posts_coords:
                if not any([x>0 and y<len(h_walls_data) and x-1<len(h_walls_data[y]) and h_walls_data[y][x-1],x<grid_size_data and y<len(h_walls_data) and x<len(h_walls_data[y]) and h_walls_data[y][x],y>0 and y-1<len(v_walls_data) and x<len(v_walls_data[y-1]) and v_walls_data[y-1][x],y<grid_size_data and y<len(v_walls_data) and x<len(v_walls_data[y]) and v_walls_data[y][x]]):
                    post_height=WALL_HEIGHT*3;special_post_created=True;is_special_post=True
            pos=(x*CELL_SIZE-offset_x,post_height/2,(grid_size_data-y)*CELL_SIZE-offset_z)
            CustomPost(position=pos,scale=(POST_DIAMETER,post_height,POST_DIAMETER),texture=textures.get('post'),is_cheese_post=is_special_post,cheese_texture=textures.get('cheese'))
    start_pos_x=(start_cell_data[1]+0.5)*CELL_SIZE-offset_x;start_pos_z=(grid_size_data-(start_cell_data[0]+0.5))*CELL_SIZE-offset_z
    return (start_pos_x,1.5,start_pos_z),floor_collider

def check_collision():
    width=1.0;length=1.0
    fr=player.world_position+(player.right*width/2)+(player.forward*length/2);fl=player.world_position+(player.right*-width/2)+(player.forward*length/2)
    br=player.world_position+(player.right*width/2)+(player.forward*-length/2);bl=player.world_position+(player.right*-width/2)+(player.forward*-length/2)
    if raycast(origin=fl,direction=player.right,distance=width-.2,ignore=(player,floor_ref)).hit: return True
    if raycast(origin=fr,direction=player.forward*-1,distance=length,ignore=(player,floor_ref)).hit: return True
    if raycast(origin=br,direction=player.right*-1,distance=width-.2,ignore=(player,floor_ref)).hit: return True
    if raycast(origin=bl,direction=player.forward,distance=length,ignore=(player,floor_ref)).hit: return True
    return False

def grid_to_minimap_pos(x, y):
    ui_x = (x / grid_size_data) - 0.5; ui_y = -((y / grid_size_data) - 0.5); return Vec2(ui_x, ui_y)

def reveal_minimap_cell(x, y):
    cell_ui_size=1/grid_size_data;wall_thickness=cell_ui_size*0.15;wall_color=color.rgba(255,0,0,100)
    if y>=0 and y<len(h_walls_data) and x<len(h_walls_data[y]) and h_walls_data[y][x]:
        Entity(parent=minimap_walls,model='quad',color=wall_color,position=grid_to_minimap_pos(x+0.5,y),scale=(cell_ui_size,wall_thickness))
    if y+1<len(h_walls_data) and x<len(h_walls_data[y+1]) and h_walls_data[y+1][x]:
        Entity(parent=minimap_walls,model='quad',color=wall_color,position=grid_to_minimap_pos(x+0.5,y+1),scale=(cell_ui_size,wall_thickness))
    if y<len(v_walls_data) and x<len(v_walls_data[y]) and v_walls_data[y][x]:
        Entity(parent=minimap_walls,model='quad',color=wall_color,position=grid_to_minimap_pos(x,y+0.5),scale=(wall_thickness,cell_ui_size))
    if y<len(v_walls_data) and x+1<len(v_walls_data[y]) and v_walls_data[y][x+1]:
        Entity(parent=minimap_walls,model='quad',color=wall_color,position=grid_to_minimap_pos(x+1,y+0.5),scale=(wall_thickness,cell_ui_size))

def flood_fill_solve(target_cells):
    q=deque();distances=[[-1 for _ in range(grid_size_data)] for _ in range(grid_size_data)]
    for gy,gx in target_cells:
        if 0<=gx<grid_size_data and 0<=gy<grid_size_data: q.append((gx,gy,0));distances[gy][gx]=0
    while q:
        x,y,dist=q.popleft()
        if y>0 and not h_walls_data[y][x] and distances[y-1][x]==-1: distances[y-1][x]=dist+1;q.append((x,y-1,dist+1))
        if y<grid_size_data-1 and not h_walls_data[y+1][x] and distances[y+1][x]==-1: distances[y+1][x]=dist+1;q.append((x,y+1,dist+1))
        if x>0 and not v_walls_data[y][x] and distances[y][x-1]==-1: distances[y][x-1]=dist+1;q.append((x-1,y,dist+1))
        if x<grid_size_data-1 and not v_walls_data[y][x+1] and distances[y][x+1]==-1: distances[y][x+1]=dist+1;q.append((x+1,y,dist+1))
    return distances

def generate_solve_actions(target_cells):
    global solve_actions
    distances = flood_fill_solve(target_cells)
    offset_x = (grid_size_data * CELL_SIZE) / 2
    offset_z = (grid_size_data * CELL_SIZE) / 2
    current_x_grid = int((player.x + offset_x) / CELL_SIZE)
    current_y_grid = grid_size_data - 1 - int((player.z + offset_z) / CELL_SIZE)

    if distances[current_y_grid][current_x_grid] == -1:
        print("Solver: No path to target.")
        solve_actions = []
        return

    # Determine the robot's current orientation to prefer straight lines from the start
    angle = round(player.rotation_y / 90) * 90 % 360
    if 315 <= angle or angle < 45: path_direction = 0  # N
    elif 45 <= angle < 135: path_direction = 1  # E
    elif 135 <= angle < 225: path_direction = 2  # S
    else: path_direction = 3  # W

    path = []
    x, y = current_x_grid, current_y_grid

    # --- MODIFIED PATH GENERATION LOOP ---
    while distances[y][x] > 0:
        current_dist = distances[y][x]
        
        # Find all valid neighbors with a shorter path to the goal
        neighbors = []
        # North (dir=0)
        if y > 0 and not h_walls_data[y][x] and distances[y-1][x] == current_dist - 1:
            neighbors.append({'x': x, 'y': y - 1, 'dir': 0})
        # East (dir=1)
        if x < grid_size_data - 1 and not v_walls_data[y][x+1] and distances[y][x+1] == current_dist - 1:
            neighbors.append({'x': x + 1, 'y': y, 'dir': 1})
        # South (dir=2)
        if y < grid_size_data - 1 and not h_walls_data[y+1][x] and distances[y+1][x] == current_dist - 1:
            neighbors.append({'x': x, 'y': y + 1, 'dir': 2})
        # West (dir=3)
        if x > 0 and not v_walls_data[y][x] and distances[y][x-1] == current_dist - 1:
            neighbors.append({'x': x - 1, 'y': y, 'dir': 3})

        if not neighbors:
            print("Solver Warning: Stuck during path generation.")
            break

        # Tie-breaking logic: prefer the neighbor that continues in the current direction
        best_neighbor = None
        if len(neighbors) > 1:
            for n in neighbors:
                if n['dir'] == path_direction:
                    best_neighbor = n
                    break
        
        # If no straight path is available, or only one path, just take the first option
        if best_neighbor is None:
            best_neighbor = neighbors[0]

        x, y = best_neighbor['x'], best_neighbor['y']
        path_direction = best_neighbor['dir'] # Update the direction for the next step
        path.append((x, y))

    # --- Action generation (remains the same) ---
    simple_actions = []
    if not path:
        solve_actions = []
        return
    
    # Get the robot's actual initial direction for generating turn commands
    angle = round(player.rotation_y / 90) * 90 % 360
    if 315 <= angle or angle < 45: current_dir = 0  # N
    elif 45 <= angle < 135: current_dir = 1  # E
    elif 135 <= angle < 225: current_dir = 2  # S
    else: current_dir = 3  # W

    last_pos = (current_x_grid, current_y_grid)
    for i in range(len(path)):
        current_pos = path[i]
        dx, dy = current_pos[0] - last_pos[0], current_pos[1] - last_pos[1]

        if dy == -1: required_dir = 0  # N
        elif dx == 1: required_dir = 1  # E
        elif dy == 1: required_dir = 2  # S
        elif dx == -1: required_dir = 3  # W
        else: continue

        turn = (required_dir - current_dir + 4) % 4
        if turn == 1: simple_actions.append('right')
        elif turn == 2: simple_actions.extend(['right', 'right'])
        elif turn == 3: simple_actions.append('left')
        
        simple_actions.append('forward')
        current_dir = required_dir
        last_pos = current_pos

    processed_actions = []
    i = 0
    while i < len(simple_actions):
        action = simple_actions[i]
        if action == 'forward':
            count = 0; j = i
            while j < len(simple_actions) and simple_actions[j] == 'forward':
                count += 1; j += 1
            processed_actions.append(('forward', count))
            i = j
        else:
            processed_actions.append(action); i += 1
    
    solve_actions = processed_actions
    print(f"Solver: Generated Route -> {solve_actions}")

# =================================================================
# ===== THIS IS THE CORRECTED UPDATE FUNCTION FROM THE VERY BEGINNING =====
# =================================================================
def update():
    global velocity,is_solving,action_in_progress,solve_actions,target_position,target_rotation
    global solve_velocity,solve_rotation_velocity,turn_direction,is_decelerating,initial_target_pos

    if is_solving:
        if not action_in_progress and solve_actions:
            action=solve_actions.pop(0); action_in_progress=True; is_decelerating=False
            if isinstance(action,str):
                if action=='align_rotation':
                    target_rotation = initial_target_pos[1]
                    delta = (target_rotation - player.rotation_y + 180) % 360 - 180
                    turn_direction = 1 if delta > 0 else -1
                elif action=='align_position': 
                    target_position=initial_target_pos[0]
                else:
                    target_rotation = player.rotation_y - 90 if action == 'left' else player.rotation_y + 90
                    turn_direction = -1 if action == 'left' else 1
            elif isinstance(action,tuple):
                move_dist = action[1]
                target_position = player.position + player.forward * CELL_SIZE * move_dist

        if action_in_progress:
            if target_position:
                # --- MODIFICATION START ---
                if dot(target_position - player.position, player.forward) < 0 or (is_decelerating and solve_velocity <= 0.01):
                    player.position=target_position; solve_velocity=0; target_position=None; action_in_progress=False
                # --- MODIFICATION END ---
                else:
                    braking_dist=(solve_velocity**2)/(2*solve_acceleration) if solve_acceleration > 0 else 0
                    if distance(player.position, target_position) <= braking_dist and not is_decelerating: is_decelerating = True
                    if is_decelerating: solve_velocity -= solve_acceleration * time.dt
                    else: solve_velocity += solve_acceleration * time.dt
                    solve_velocity = clamp(solve_velocity, 0, max_solve_speed)
                    player.position += player.forward * solve_velocity * time.dt
            elif target_rotation is not None:
                # --- MODIFICATION START ---
                if (turn_direction * (target_rotation - player.rotation_y)) < 0.1 or (is_decelerating and solve_rotation_velocity <= 0.1):
                    player.rotation_y = target_rotation % 360; solve_rotation_velocity=0; target_rotation=None; action_in_progress=False
                # --- MODIFICATION END ---
                else:
                    braking_angle = (solve_rotation_velocity**2)/(2*solve_rotation_acceleration) if solve_rotation_acceleration > 0 else 0
                    if abs(target_rotation - player.rotation_y) <= braking_angle and not is_decelerating: is_decelerating = True
                    if is_decelerating: solve_rotation_velocity -= solve_rotation_acceleration * time.dt
                    else: solve_rotation_velocity += solve_rotation_acceleration * time.dt
                    solve_rotation_velocity = clamp(solve_rotation_velocity, 0, max_solve_rotation_speed)
                    player.rotation_y += solve_rotation_velocity * turn_direction * time.dt

        if not solve_actions and not action_in_progress:
            is_solving=False; print("Solver: Run complete.")
    
    if not is_solving and not free_fly_camera.enabled:
        original_rotation=player.rotation_y; player.rotation_y+=(held_keys['right arrow']-held_keys['left arrow'])*time.dt*turn_speed
        if check_collision(): player.rotation_y=original_rotation
        acceleration_direction=(held_keys['up arrow']-held_keys['down arrow'])
        velocity+=player.forward*acceleration_direction*acceleration*time.dt
        forward_speed=dot(velocity,player.forward); sideways_speed=dot(velocity,player.right)
        forward_velocity=player.forward*forward_speed; sideways_velocity=player.right*sideways_speed
        forward_velocity-=forward_velocity*friction*time.dt; sideways_velocity-=sideways_velocity*(friction*1.5)*time.dt
        velocity=forward_velocity+sideways_velocity; move_amount=velocity*time.dt
        original_x=player.x; player.x+=move_amount.x
        if check_collision(): player.x=original_x; velocity.x=0
        original_z=player.z; player.z+=move_amount.z
        if check_collision(): player.z=original_z; velocity.z=0
        if not raycast(player.world_position,(0,-1,0),distance=robot_height*0.51,ignore=[player,]).hit: player.y-=gravity*time.dt
    
    camera_rig.position=player.position; camera_rig.rotation_y=player.rotation_y
    if 'top_down_cam' in globals() and top_down_cam and top_down_cam.enabled:
        top_down_cam.x=player.x; top_down_cam.z=player.z; top_down_cam.y=zoom_level
    if map_pivot:
        offset_x=(grid_size_data*CELL_SIZE)/2; offset_z=(grid_size_data*CELL_SIZE)/2
        grid_x=(player.x+offset_x)/CELL_SIZE; grid_y=grid_size_data-((player.z+offset_z)/CELL_SIZE)
        map_pivot.rotation_z=-player.rotation_y; map_content.position=-grid_to_minimap_pos(grid_x,grid_y)
        cell_x,cell_y=int(grid_x),int(grid_y)
        if 0<=cell_x<grid_size_data and 0<=cell_y<grid_size_data:
            if (cell_x,cell_y) not in seen_cells: seen_cells.add((cell_x,cell_y)); reveal_minimap_cell(cell_x,cell_y)

def update_main_camera_view():
    if is_chase_cam: camera.position=(0,robot_height*1.5,-1.5); player.visible=True
    else: camera.position=(0,robot_height,0); player.visible=False

def input(key):
    global zoom_level,is_chase_cam,free_fly_camera,is_solving,velocity,solve_actions,action_in_progress
    global solve_velocity,solve_rotation_velocity,target_position,target_rotation,initial_target_pos, top_down_cam
    if key=='f':
        if not free_fly_camera.enabled: free_fly_camera.world_position=camera.world_position; free_fly_camera.world_rotation=camera.world_rotation
        free_fly_camera.enabled=not free_fly_camera.enabled; camera_rig.enabled=not free_fly_camera.enabled
        player.visible=free_fly_camera.enabled or is_chase_cam
    if key=='s' and not free_fly_camera.enabled:
        if not is_solving:
            velocity=Vec3(0,0,0); solve_velocity=0.0; solve_rotation_velocity=0.0
            offset_x=(grid_size_data*CELL_SIZE)/2; offset_z=(grid_size_data*CELL_SIZE)/2
            grid_x=int((player.x+offset_x)/CELL_SIZE); grid_y=grid_size_data-1-int((player.z+offset_z)/CELL_SIZE)
            center_pos = Vec3((grid_x+0.5)*CELL_SIZE-offset_x, player.y, (grid_size_data-(grid_y+0.5))*CELL_SIZE-offset_z)
            is_at_goal = (grid_y, grid_x) in goal_cells_set
            if is_at_goal:
                print("Solver: At goal! Solving back to start..."); generate_solve_actions(target_cells=[start_cell_data])
            else:
                print("Solver: Solving to goal..."); generate_solve_actions(target_cells=goal_cells_data)
            required_start_rot = round(player.rotation_y / 90) * 90
            initial_target_pos = (center_pos, required_start_rot)
            alignment_actions = []
            delta_rot = (required_start_rot - player.rotation_y + 180) % 360 - 180
            if abs(delta_rot) > 1: alignment_actions.append('align_rotation')
            if distance(player.position, center_pos) > 0.05: alignment_actions.append('align_position')
            solve_actions = alignment_actions + solve_actions
            is_solving = True
        else:
            print("Solver: Run interrupted by user. Returning to manual control.")
            is_solving=False; solve_actions=[]; action_in_progress=False
            target_position=None; target_rotation=None; solve_velocity=0.0; solve_rotation_velocity=0.0
    if free_fly_camera.enabled:
        if key=='scroll up': free_fly_camera.y+=1
        if key=='scroll down': free_fly_camera.y-=1
    if not free_fly_camera.enabled:
        if key=='m' and minimap: minimap.enabled=not minimap.enabled
        if key=='tab':
            camera.enabled=not camera.enabled; top_down_cam.enabled=not top_down_cam.enabled
            player.visible=top_down_cam.enabled or is_chase_cam
        if key=='v' and camera.enabled: is_chase_cam=not is_chase_cam; update_main_camera_view()
        if 'top_down_cam' in globals() and top_down_cam and top_down_cam.enabled:
            if key=='scroll up': zoom_level-=2
            if key=='scroll down': zoom_level+=2; zoom_level=clamp(zoom_level,5,50)

if __name__ == '__main__':
    app=Ursina(); app.development_mode=False; sky=Sky()
    textures={
        'wall':load_texture('wall_texture'),'wall_top':load_texture('wall_top_texture'),
        'post':load_texture('post_texture'),'floor':load_texture('floor_texture'),
        'robot_body':load_texture('robot_body_texture'),'cheese':load_texture('cheese_texture'),
        'goal_floor':load_texture('goal_floor_texture')
    }
    player_start_position,floor_ref = create_maze_from_json(JSON_FILE_PATH,textures)
    if not floor_ref: print("Exiting due to maze loading failure."); sys.exit()
    
    player=Entity(position=player_start_position,rotation=(0,0,0),model='cube',scale=(0.8,robot_height,1.0),texture=textures.get('robot_body'),color=color.white if textures.get('robot_body') else color.dark_gray,visible=False)
    
    camera_rig=Entity(position=player.position,rotation_y=player.rotation_y)
    camera.parent=camera_rig
    update_main_camera_view()

    zoom_level=grid_size_data*1.8
    top_down_cam=EditorCamera(rotation=(90,0,0),position=(0,zoom_level,0),enabled=False)
    free_fly_camera=EditorCamera(enabled=False,rotation_speed=100)
    
    map_size=0.4
    minimap=Entity(parent=camera.ui,scale=map_size,position=(window.aspect_ratio*0.5-map_size*0.5-0.01,0.5-map_size*0.5-0.01),enabled=False)
    map_pivot=Entity(parent=minimap);map_content=Entity(parent=map_pivot)
    
    goal_color=color.black33
    for cell in goal_cells_data:
        pos=grid_to_minimap_pos(cell[1]+0.5,cell[0]+0.5)
        Entity(parent=map_content,model='quad',color=goal_color,position=pos,scale=1/grid_size_data,z=2)
    
    minimap_walls=Entity(parent=map_content,z=1)
    player_marker_ui=Entity(parent=minimap,z=0)
    Entity(parent=player_marker_ui,model='circle',color=color.blue,scale=(1/grid_size_data)*0.6)
    Entity(parent=player_marker_ui,model='quad',color=color.white,scale=((1/grid_size_data)*0.1,(1/grid_size_data)*0.4),origin=(0,-0.5))
    
    window.title='Micromouse 3D Maze Viewer (S: Solve/Stop, M: Minimap, F: Free-Cam)';window.borderless=False
    window.fullscreen=False;window.exit_button.visible=False;window.fps_counter.enabled=True
    
    app.run()