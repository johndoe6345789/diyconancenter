#!/usr/bin/env python3
"""Generate an index page for the DIY Conan Center repository."""

import os
import yaml
import json
from pathlib import Path
from datetime import datetime

def get_package_info(recipe_path):
    """Extract package information from a recipe directory."""
    package_name = recipe_path.name
    versions = []
    
    # Look for config.yml
    config_file = recipe_path / "config.yml"
    if config_file.exists():
        with open(config_file, 'r') as f:
            config = yaml.safe_load(f)
            if config and 'versions' in config:
                versions = list(config['versions'].keys())
    
    # If no config.yml, check for version directories
    if not versions:
        for item in recipe_path.iterdir():
            if item.is_dir() and not item.name.startswith('.'):
                versions.append(item.name)
    
    description = ""
    # Try to get description from first conanfile.py
    for version_dir in recipe_path.iterdir():
        if version_dir.is_dir():
            conanfile = version_dir / "conanfile.py"
            if conanfile.exists():
                with open(conanfile, 'r') as f:
                    content = f.read()
                    # Simple extraction of description
                    for line in content.split('\n'):
                        if 'description =' in line:
                            description = line.split('=', 1)[1].strip().strip('"\'')
                            break
                break
    
    return {
        'name': package_name,
        'versions': sorted(versions),
        'description': description
    }

def generate_html(packages):
    """Generate HTML index page."""
    html = """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>DIY Conan Center</title>
    <style>
        * {
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }
        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Oxygen, Ubuntu, Cantarell, sans-serif;
            line-height: 1.6;
            color: #333;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            min-height: 100vh;
            padding: 20px;
        }
        .container {
            max-width: 1200px;
            margin: 0 auto;
            background: white;
            border-radius: 10px;
            box-shadow: 0 10px 40px rgba(0,0,0,0.2);
            overflow: hidden;
        }
        header {
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 40px;
            text-align: center;
        }
        header h1 {
            font-size: 2.5em;
            margin-bottom: 10px;
        }
        header p {
            font-size: 1.2em;
            opacity: 0.9;
        }
        .stats {
            display: flex;
            justify-content: space-around;
            background: #f8f9fa;
            padding: 20px;
            border-bottom: 2px solid #e9ecef;
        }
        .stat {
            text-align: center;
        }
        .stat-number {
            font-size: 2em;
            font-weight: bold;
            color: #667eea;
        }
        .stat-label {
            color: #6c757d;
            text-transform: uppercase;
            font-size: 0.9em;
            letter-spacing: 1px;
        }
        .search-bar {
            padding: 20px 40px;
            background: white;
        }
        .search-input {
            width: 100%;
            padding: 15px;
            font-size: 1em;
            border: 2px solid #e9ecef;
            border-radius: 5px;
            transition: border-color 0.3s;
        }
        .search-input:focus {
            outline: none;
            border-color: #667eea;
        }
        .packages {
            padding: 20px 40px 40px;
        }
        .package-card {
            background: white;
            border: 2px solid #e9ecef;
            border-radius: 8px;
            padding: 20px;
            margin-bottom: 15px;
            transition: all 0.3s;
        }
        .package-card:hover {
            border-color: #667eea;
            box-shadow: 0 4px 12px rgba(102, 126, 234, 0.15);
            transform: translateY(-2px);
        }
        .package-name {
            font-size: 1.5em;
            font-weight: bold;
            color: #667eea;
            margin-bottom: 10px;
        }
        .package-description {
            color: #6c757d;
            margin-bottom: 10px;
        }
        .package-versions {
            display: flex;
            flex-wrap: wrap;
            gap: 8px;
        }
        .version-badge {
            background: #e9ecef;
            padding: 4px 12px;
            border-radius: 15px;
            font-size: 0.9em;
            color: #495057;
        }
        .no-results {
            text-align: center;
            padding: 40px;
            color: #6c757d;
            font-size: 1.2em;
        }
        footer {
            text-align: center;
            padding: 20px;
            background: #f8f9fa;
            color: #6c757d;
            border-top: 2px solid #e9ecef;
        }
        .install-command {
            background: #f8f9fa;
            padding: 10px;
            border-radius: 5px;
            font-family: monospace;
            margin-top: 10px;
            border-left: 4px solid #667eea;
        }
    </style>
</head>
<body>
    <div class="container">
        <header>
            <h1>🚀 DIY Conan Center</h1>
            <p>Your Personal C/C++ Package Repository</p>
        </header>
        
        <div class="stats">
            <div class="stat">
                <div class="stat-number" id="total-packages">""" + str(len(packages)) + """</div>
                <div class="stat-label">Packages</div>
            </div>
            <div class="stat">
                <div class="stat-number" id="total-versions">""" + str(sum(len(p['versions']) for p in packages)) + """</div>
                <div class="stat-label">Versions</div>
            </div>
            <div class="stat">
                <div class="stat-number">""" + datetime.now().strftime("%Y-%m-%d") + """</div>
                <div class="stat-label">Last Updated</div>
            </div>
        </div>
        
        <div class="search-bar">
            <input type="text" id="search" class="search-input" placeholder="🔍 Search packages..." onkeyup="filterPackages()">
        </div>
        
        <div class="packages" id="packages">
"""
    
    for package in sorted(packages, key=lambda x: x['name']):
        html += f"""            <div class="package-card" data-name="{package['name'].lower()}">
                <div class="package-name">{package['name']}</div>
                <div class="package-description">{package['description'] or 'No description available'}</div>
                <div class="package-versions">
"""
        for version in package['versions']:
            html += f"""                    <span class="version-badge">{version}</span>
"""
        html += """                </div>
                <div class="install-command">
                    conan install --requires=""" + package['name'] + """/{version}
                </div>
            </div>
"""
    
    html += """        </div>
        
        <footer>
            <p>Generated on """ + datetime.now().strftime("%Y-%m-%d %H:%M:%S UTC") + """</p>
            <p>Built with ❤️ using GitHub Actions</p>
        </footer>
    </div>
    
    <script>
        function filterPackages() {
            const searchTerm = document.getElementById('search').value.toLowerCase();
            const packages = document.querySelectorAll('.package-card');
            let visibleCount = 0;
            
            packages.forEach(package => {
                const name = package.getAttribute('data-name');
                if (name.includes(searchTerm)) {
                    package.style.display = 'block';
                    visibleCount++;
                } else {
                    package.style.display = 'none';
                }
            });
            
            // Show "no results" message if needed
            const packagesContainer = document.getElementById('packages');
            const existingNoResults = packagesContainer.querySelector('.no-results');
            
            if (visibleCount === 0 && !existingNoResults) {
                const noResults = document.createElement('div');
                noResults.className = 'no-results';
                noResults.textContent = 'No packages found matching your search.';
                packagesContainer.appendChild(noResults);
            } else if (visibleCount > 0 && existingNoResults) {
                existingNoResults.remove();
            }
        }
    </script>
</body>
</html>
"""
    return html

def main():
    """Main function to generate the index."""
    repo_root = Path(__file__).parent.parent
    recipes_dir = repo_root / "recipes"
    docs_dir = repo_root / "docs"
    
    # Ensure docs directory exists
    docs_dir.mkdir(exist_ok=True)
    
    # Collect package information
    packages = []
    if recipes_dir.exists():
        for recipe_path in recipes_dir.iterdir():
            if recipe_path.is_dir() and not recipe_path.name.startswith('.'):
                package_info = get_package_info(recipe_path)
                packages.append(package_info)
    
    # Generate HTML
    html = generate_html(packages)
    
    # Write index.html
    index_file = docs_dir / "index.html"
    with open(index_file, 'w') as f:
        f.write(html)
    
    print(f"Generated index with {len(packages)} packages")
    print(f"Index file: {index_file}")
    
    # Also generate a JSON file with package data
    json_file = docs_dir / "packages.json"
    with open(json_file, 'w') as f:
        json.dump(packages, f, indent=2)
    
    print(f"Package data: {json_file}")

if __name__ == "__main__":
    main()
