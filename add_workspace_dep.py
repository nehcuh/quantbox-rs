#!/usr/bin/env python3
# add_workspace_dep.py

import sys
import subprocess
import os
from pathlib import Path
import toml

def read_toml_file(file_path):
    try:
        with open(file_path, 'r') as f:
            return toml.load(f)
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return {}

def write_toml_file(file_path, data):
    try:
        with open(file_path, 'w') as f:
            # Write workspace section
            f.write("[workspace]\n")
            if 'workspace' in data and 'members' in data['workspace']:
                f.write("members = [\n")
                for member in data['workspace']['members']:
                    f.write(f'    "{member}",\n')
                f.write("]\n\n")

            # Write dependencies section
            if 'workspace' in data and 'dependencies' in data['workspace']:
                f.write("[workspace.dependencies]\n")
                deps = data['workspace']['dependencies']
                for name, value in sorted(deps.items()):
                    if isinstance(value, dict):
                        items = []
                        for k, v in value.items():
                            if isinstance(v, list):
                                v_str = f'[{", ".join(f'"{x}"' for x in v)}]'
                                items.append(f'{k} = {v_str}')
                            else:
                                items.append(f'{k} = "{v}"')
                        f.write(f'{name} = {{ {", ".join(items)} }}\n')
                    else:
                        f.write(f'{name} = "{value}"\n')
    except Exception as e:
        print(f"Error writing {file_path}: {e}")
        raise

def add_workspace_dependency(dep_spec):
    # Parse dependency spec (format: "dep_name:features" or just "dep_name")
    if ':' in dep_spec:
        dep, features = dep_spec.split(':', 1)
    else:
        dep, features = dep_spec, None

    # Store the original directory
    original_dir = Path.cwd()
    workspace_root = original_dir
    qb_core_dir = workspace_root / 'qb-core'
    
    try:
        if not qb_core_dir.exists():
            raise RuntimeError("qb-core directory not found. Please run this script from the workspace root.")

        # Read current workspace Cargo.toml
        workspace_toml = workspace_root / 'Cargo.toml'
        workspace_data = read_toml_file(workspace_toml)

        # Ensure workspace structure exists
        if 'workspace' not in workspace_data:
            workspace_data['workspace'] = {}
        if 'dependencies' not in workspace_data['workspace']:
            workspace_data['workspace']['dependencies'] = {}

        # 临时添加到 qb-core
        os.chdir(qb_core_dir)

        # 构建 cargo add 命令
        cmd = ['cargo', 'add', dep]
        if features:
            cmd.extend(['--features', features])

        # 执行添加命令
        subprocess.run(cmd, check=True, capture_output=True, text=True)

        # 读取新添加的依赖信息
        qb_core_data = read_toml_file('Cargo.toml')
        if dep not in qb_core_data.get('dependencies', {}):
            raise RuntimeError(f"Failed to find dependency {dep} in qb-core/Cargo.toml")

        # Get the dependency specification
        dep_value = qb_core_data['dependencies'][dep]

        # 删除临时依赖
        subprocess.run(['cargo', 'remove', dep], check=True, capture_output=True, text=True)

        # 返回上级目录
        os.chdir(workspace_root)

        # Add or update dependency in workspace
        workspace_data['workspace']['dependencies'][dep] = dep_value

        # Write back the workspace Cargo.toml
        write_toml_file(workspace_toml, workspace_data)

        print(f"Successfully added {dep} to workspace dependencies")
        if isinstance(dep_value, dict):
            items = [f'{k} = {repr(v)}' for k, v in dep_value.items()]
            return f"{dep} = {{ {', '.join(items)} }}"
        else:
            return f'{dep} = "{dep_value}"'

    except subprocess.CalledProcessError as e:
        print(f"Error executing cargo command: {e.stderr if hasattr(e, 'stderr') else str(e)}")
        raise
    except Exception as e:
        print(f"Error: {str(e)}")
        raise
    finally:
        # 确保总是返回到原始目录
        os.chdir(original_dir)

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: python add_workspace_dep.py dep_name[:features]")
        print("Example: python add_workspace_dep.py serde:derive")
        print("         python add_workspace_dep.py tokio:full")
        sys.exit(1)

    dep_spec = sys.argv[1]
    try:
        add_workspace_dependency(dep_spec)
    except Exception as e:
        print(f"Failed to add workspace dependency: {e}")
        sys.exit(1)
