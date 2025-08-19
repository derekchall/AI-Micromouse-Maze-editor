import json
from ursina import *
import os # Import the os library

# Get the directory where this script is located
script_dir = os.path.dirname(os.path.abspath(__file__))
# Create a full, absolute path to the JSON file
JSON_FILE_PATH = os.path.join(script_dir, 'maze_3d_data.json')

def dot(v1, v2):
    return v1.x*v2.x + v1.y*v2.y + v1.z*v2.z

class CustomWall(Entity):
    def __init__(self, position=(0, 0, 0), scale=(1, 1, 1), main_texture=None, top_texture=None, **kwargs):
        super().__init__(
            position=position,
            scale=scale,
            collider='box'
        )
        Entity(parent=self, model='cube', texture=main_texture, color=color.white, scale=(1, 0.98, 1), position=(0, -0.01, 0))
        Entity(parent=self, model='cube', texture=top_texture, color=color.red, scale=(1, 0.02, 1), position=(0, 0.49, 0))

# --- MODIFIED: Complete rewrite of the cheese mesh with geometrically correct faces ---
class CustomPost(Entity):
    def __init__(self, position=(0, 0, 0), scale=(1, 1, 1), texture=None, is_cheese_post=False, cheese_texture=None, **kwargs):
        post_color = color.white if texture else color.yellow
        super().__init__(model='cube', texture=texture, color=post_color, position=position, scale=scale, collider='box', **kwargs)

        if is_cheese_post:
            # --- THIS IS THE FIX ---
            # Define 6 corner positions for a geometrically correct triangular prism
            bbl = Vec3(-0.5, -0.5, -0.5)  # Bottom-Back-Left
            bbr = Vec3(0.5, -0.5, -0.5)   # Bottom-Back-Right
            tbl = Vec3(-0.5, 0.5, -0.5)   # Top-Back-Left
            bfl = Vec3(-0.5, -0.5, 0.5)   # Bottom-Front-Left
            bfr = Vec3(0.5, -0.5, 0.5)    # Bottom-Front-Right
            tfl = Vec3(-0.5, 0.5, 0.5)    # Top-Front-Left

            # Define vertices and UVs for each face independently to ensure correct texturing
            vertices = [
                # Back Face (triangle)
                bbl, bbr, tbl,
                # Front Face (triangle)
                bfl, tfl, bfr,
                # Bottom Face (quad) - All points on y=-0.5 plane
                bbl, bfl, bfr, bbr,
                # Vertical Face (quad) - All points on x=-0.5 plane
                bbl, tbl, tfl, bfl,
                # Sloped Face (quad) - Connects the back-right and front-left edges
                bbr, bfr, tfl, tbl,
            ]
            
            uvs = [
                # UVs for Back Face
                Vec2(0,0), Vec2(1,0), Vec2(0,1),
                # UVs for Front Face
                Vec2(0,0), Vec2(0,1), Vec2(1,0),
                # UVs for Bottom Face
                Vec2(0,0), Vec2(0,1), Vec2(1,1), Vec2(1,0),
                # UVs for Vertical Face
                Vec2(0,0), Vec2(1,0), Vec2(1,1), Vec2(0,1),
                # UVs for Sloped Face
                Vec2(0,0), Vec2(1,0), Vec2(1,1), Vec2(0,1),
            ]

            # Define triangles using indices into the new 'vertices' list
            tris = [
                0, 1, 2,                # Back Face
                3, 4, 5,                # Front Face
                6, 7, 8, 6, 8, 9,      # Bottom Face
                10, 11, 12, 10, 12, 13, # Vertical Face
                14, 15, 16, 14, 16, 17, # Sloped Face
            ]

            cheese_wedge_model = Mesh(vertices=vertices, triangles=tris, uvs=uvs, mode='triangle')
            cheese_wedge_model.generate_normals()

            desired_world_scale = Vec3(0.6, 0.5, 0.8)
            parent_world_scale = scale
            cheese_local_scale = (
                desired_world_scale.x / parent_world_scale[0],
                desired_world_scale.y / parent_world_scale[1],
                desired_world_scale.z / parent_world_scale[2]
            )
            cheese_y_pos = 0.5 + (cheese_local_scale[1] * 0.5)

            self.cheese = Entity(
                parent=self,
                model=cheese_wedge_model,
                texture=cheese_texture,
                color=color.white if cheese_texture else color.gold,
                y=cheese_y_pos,
                scale=cheese_local_scale,
                rotation=(0, -90, 0) # Rotate to face forward
            )


def create_maze_from_json(JSON_FILE_PATH, textures):
    """
    Loads a Micromouse maze structure and applies textures, with correct orientation and fallbacks.
    """
    try:
        with open(JSON_FILE_PATH, 'r') as f:
            maze_data = json.load(f)
    except FileNotFoundError:
        print(f"Error: The file '{JSON_FILE_PATH}' was not found.")
        return None, 0, None
    except json.JSONDecodeError:
        print(f"Error: Could not decode the JSON file '{JSON_FILE_PATH}'.")
        return None, 0, None

    CELL_SIZE = 1.8
    WALL_HEIGHT = 0.5
    WALL_THICKNESS = 0.12
    POST_DIAMETER = 0.12
    GAP_SIZE = 0

    grid_size = maze_data.get("grid_size", 16)
    h_walls = maze_data.get("h_walls", [])
    v_walls = maze_data.get("v_walls", [])
    start_cell = maze_data.get("start_cell", [0, 0])

    offset_x = (grid_size * CELL_SIZE) / 2
    offset_z = (grid_size * CELL_SIZE) / 2

    floor = Entity(
        model='plane',
        scale=(grid_size * CELL_SIZE, 1, grid_size * CELL_SIZE),
        texture=textures.get('floor'),
        texture_scale=(grid_size, grid_size),
        color=color.white if textures.get('floor') else color.black,
        collider='box'
    )

    wall_length = CELL_SIZE - POST_DIAMETER - (2 * GAP_SIZE)

    for y, row in enumerate(h_walls):
        for x, wall_exists in enumerate(row):
            if wall_exists:
                z_pos = (grid_size - y) * CELL_SIZE - offset_z
                pos = (x * CELL_SIZE - offset_x + CELL_SIZE / 2, WALL_HEIGHT / 2, z_pos)
                scl = (wall_length, WALL_HEIGHT, WALL_THICKNESS)
                CustomWall(position=pos, scale=scl, main_texture=textures.get('wall'), top_texture=textures.get('wall_top'))

    for y, row in enumerate(v_walls):
        for x, wall_exists in enumerate(row):
            if wall_exists:
                z_pos = ((grid_size - 1 - y) * CELL_SIZE - offset_z) + CELL_SIZE / 2
                pos = (x * CELL_SIZE - offset_x, WALL_HEIGHT / 2, z_pos)
                scl = (WALL_THICKNESS, WALL_HEIGHT, wall_length)
                CustomWall(position=pos, scale=scl, main_texture=textures.get('wall'), top_texture=textures.get('wall_top'))

    target_cells = maze_data.get("goal_cells", [])
    target_posts_coords = set()

    if target_cells:
        min_x = min(cell[1] for cell in target_cells)
        max_x = max(cell[1] for cell in target_cells)
        min_y = min(cell[0] for cell in target_cells)
        max_y = max(cell[0] for cell in target_cells)

        for x in range(min_x, max_x + 2):
            for y in range(min_y, max_y + 2):
                target_posts_coords.add((x, y))
    else:
        center = grid_size // 2
        for x in range(center - 1, center + 2):
            for y in range(center - 1, center + 2):
                target_posts_coords.add((x, y))

    special_post_created = False

    for y in range(grid_size + 1):
        for x in range(grid_size + 1):
            post_height = WALL_HEIGHT
            is_special_post = False

            if not special_post_created and (x, y) in target_posts_coords:
                has_wall_left = x > 0 and y < len(h_walls) and x-1 < len(h_walls[y]) and h_walls[y][x-1]
                has_wall_right = x < grid_size and y < len(h_walls) and x < len(h_walls[y]) and h_walls[y][x]
                has_wall_down = y > 0 and y-1 < len(v_walls) and x < len(v_walls[y-1]) and v_walls[y-1][x]
                has_wall_up = y < grid_size and y < len(v_walls) and x < len(v_walls[y]) and v_walls[y][x]

                if not any([has_wall_left, has_wall_right, has_wall_down, has_wall_up]):
                    post_height = WALL_HEIGHT * 3
                    special_post_created = True
                    is_special_post = True

            z_pos = (grid_size - y) * CELL_SIZE - offset_z
            pos = (x * CELL_SIZE - offset_x, post_height / 2, z_pos)
            scl = (POST_DIAMETER, post_height, POST_DIAMETER)

            CustomPost(
                position=pos,
                scale=scl,
                texture=textures.get('post'),
                is_cheese_post=is_special_post,
                cheese_texture=textures.get('cheese')
            )

    start_pos_x = (start_cell[1] + 0.5) * CELL_SIZE - offset_x
    start_pos_z = (grid_size - (start_cell[0] + 0.5)) * CELL_SIZE - offset_z

    return (start_pos_x, 1.5, start_pos_z), grid_size, floor


def check_collision():
    width = 1.0
    length = 1.0
    fr = player.world_position + (player.right * width/2) + (player.forward * length/2)
    fl = player.world_position + (player.right * -width/2) + (player.forward * length/2)
    br = player.world_position + (player.right * width/2) + (player.forward * -length/2)
    bl = player.world_position + (player.right * -width/2) + (player.forward * -length/2)

    if raycast(origin=fl, direction=player.right, distance=width-.2, ignore=(player, floor_ref)).hit: return True
    if raycast(origin=fr, direction=player.forward * -1, distance=length, ignore=(player, floor_ref)).hit: return True
    if raycast(origin=br, direction=player.right * -1, distance=width-.2, ignore=(player, floor_ref)).hit: return True
    if raycast(origin=bl, direction=player.forward, distance=length, ignore=(player, floor_ref)).hit: return True
    return False


def update():
    global velocity
    
    if whiskers and whiskers[0].enabled:
        width = 1.0
        length = 1.0
        y_offset = player.up * 0.8
        fr = player.world_position + (player.right * width/2) + (player.forward * length/2) + y_offset
        fl = player.world_position + (player.right * -width/2) + (player.forward * length/2) + y_offset
        br = player.world_position + (player.right * width/2) + (player.forward * -length/2) + y_offset
        bl = player.world_position + (player.right * -width/2) + (player.forward * -length/2) + y_offset
        whiskers[0].model.vertices = [fl, fr]
        whiskers[1].model.vertices = [fr, br]
        whiskers[2].model.vertices = [br, bl]
        whiskers[3].model.vertices = [bl, fl]
        for w in whiskers: w.model.generate()

    original_rotation = player.rotation_y
    player.rotation_y += (held_keys['right arrow'] - held_keys['left arrow']) * time.dt * turn_speed
    if check_collision():
        player.rotation_y = original_rotation

    acceleration_direction = (held_keys['up arrow'] - held_keys['down arrow'])
    velocity += player.forward * acceleration_direction * acceleration * time.dt
    
    forward_speed = dot(velocity, player.forward)
    sideways_speed = dot(velocity, player.right)
    forward_velocity = player.forward * forward_speed
    sideways_velocity = player.right * sideways_speed
    forward_velocity -= forward_velocity * friction * time.dt
    sideways_velocity -= sideways_velocity * (friction * 1.5) * time.dt
    velocity = forward_velocity + sideways_velocity

    move_amount = velocity * time.dt
    
    original_x = player.x
    player.x += move_amount.x
    if check_collision():
        player.x = original_x
        velocity.x = 0
            
    original_z = player.z
    player.z += move_amount.z
    if check_collision():
        player.z = original_z
        velocity.z = 0

    ground_check = raycast(player.world_position, (0, -1, 0), distance=robot_height * 0.51, ignore=[player,])
    if not ground_check.hit:
        player.y -= gravity * time.dt
    
    camera_rig.position = player.position
    camera_rig.rotation_y = player.rotation_y

    if top_down_cam.enabled:
        top_down_cam.x = player.x
        top_down_cam.z = player.z
        top_down_cam.y = zoom_level


def update_main_camera_view():
    if is_chase_cam:
        camera.position = (0, robot_height * 1.5, -1.5)
        player.visible = True
    else:
        camera.position = (0, robot_height, 0)
        player.visible = False

def input(key):
    global zoom_level, is_chase_cam

    if key == 'tab':
        camera.enabled = not camera.enabled
        top_down_cam.enabled = not top_down_cam.enabled
        player.visible = top_down_cam.enabled or is_chase_cam

    if key == 'v':
        if camera.enabled:
            is_chase_cam = not is_chase_cam
            update_main_camera_view()
    
    if key == 'c':
        if whiskers:
            for w in whiskers:
                w.enabled = not w.enabled

    if top_down_cam.enabled:
        if key == 'scroll up': zoom_level -= 2
        if key == 'scroll down': zoom_level += 2
        zoom_level = clamp(zoom_level, 5, 50)


if __name__ == '__main__':
    app = Ursina()
    app.development_mode = False
    
    sky = Sky()

    textures = {
        'wall': load_texture('wall_texture'),
        'wall_top': load_texture('wall_top_texture'),
        'post': load_texture('post_texture'),
        'floor': load_texture('floor_texture'),
        'robot_body': load_texture('robot_body_texture'),
        'cheese': load_texture('cheese_texture')
    }

    player_start_position, maze_grid_size, floor_ref = create_maze_from_json(JSON_FILE_PATH, textures)

    turn_speed = 125
    acceleration = 20
    friction = 2.0
    velocity = Vec3(0,0,0)
    gravity = 1
    is_chase_cam = False
    whiskers = None
    robot_height = 0.25
    
    if player_start_position:
        player = Entity(
            position=player_start_position,
            rotation=(0,0,0),
            model='cube',
            scale=(0.8, robot_height, 1.0),
            texture=textures.get('robot_body'),
            color=color.white if textures.get('robot_body') else color.dark_gray,
            visible=False
        )
        
        camera_rig = Entity(position=player.position, rotation_y=player.rotation_y)
        camera.parent = camera_rig
        camera.position = (0, robot_height, 0)
        
        whiskers = [Entity(model=Mesh(mode='line'), color=color.orange, enabled=False) for _ in range(4)]
        
        zoom_level = maze_grid_size * 1.8
        top_down_cam = EditorCamera(
            rotation=(90, 0, 0),
            position=(0, zoom_level, 0),
            enabled=False
        )
        
    window.title = 'Micromouse 3D Maze Viewer (Tab: Top-Down, V: FPV/Chase)'
    window.borderless = False
    window.fullscreen = False
    window.exit_button.visible = False
    window.fps_counter.enabled = True

    app.run()