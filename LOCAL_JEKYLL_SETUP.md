# Local Jekyll Setup

How to preview the site locally before pushing to GitHub Pages.

## What each file does

| File | Purpose |
|------|---------|
| `_config.yml` | Site-wide settings: theme, title, URL, plugins, and default layout |
| `Gemfile` | Lists Ruby dependencies (Jekyll, theme, plugins). Bundler reads this |
| `Gemfile.lock` | Auto-generated lock of exact gem versions for reproducible builds |
| `_layouts/` | Custom page layouts. `medieval.html` is a layout tailored for long Latin logic texts |
| `markdown-preview.css` | VS Code Markdown Preview stylesheet for `.textus` blocks (local editing aid only) |
| `.gitignore` | Tells git to ignore `_site/`, caches, and Bundler output |

The `_site/` folder is the **generated output** — Jekyll builds it from your Markdown files. Never edit files inside `_site/` directly.

## First-time setup

### 1. Install Ruby (if not already installed)

```bash
sudo apt install ruby-full build-essential
```

### 2. Install Bundler

```bash
sudo gem install bundler
```

### 3. Install project dependencies

From the project root:

```bash
cd Spanish-Logicians-at-the-University-of-Paris
bundle install
```

This reads the `Gemfile` and installs Jekyll, the theme, and all plugins.

## Running the local server

Always use `bundle exec` to ensure the correct gem versions are used:

```bash
bundle exec jekyll serve
```

The site will be available at:

```
http://127.0.0.1:4000/Spanish-Logicians-at-the-University-of-Paris/
```

Open any page by appending its path, e.g.:

```
http://127.0.0.1:4000/Spanish-Logicians-at-the-University-of-Paris/philosophers/John-Mair/Introdvctorium-in-Aristotelicam-Dialecticen-1521
```

Press `Ctrl+C` in the terminal to stop the server.

### Auto-regeneration

Jekyll watches for file changes and rebuilds automatically. Just save your file and refresh the browser. If you change `_config.yml`, you must restart the server.

## Updating gems

To update all gems to their latest compatible versions:

```bash
bundle update
```

To update a specific gem:

```bash
bundle update jekyll
```

After updating, the `Gemfile.lock` will reflect the new versions. Commit it so builds stay reproducible.

## Trying new things safely

1. **Start the server**: `bundle exec jekyll serve`
2. **Edit any `.md` file** or layout — the site rebuilds in seconds
3. **Refresh the browser** to see changes
4. **When satisfied**, commit and push to GitHub:
   ```bash
   git add .
   git commit -m "description of changes"
   git push
   ```
5. **If something breaks**, just revert before pushing:
   ```bash
   git checkout -- path/to/file
   ```

## Layouts

Pages use the layout specified in their YAML front matter:

```yaml
---
layout: medieval
title: "My Page Title"
---
```

- **No `layout:` specified** → uses `default` (the minimal theme's layout, configured in `_config.yml` under `defaults`)
- **`layout: medieval`** → uses `_layouts/medieval.html`, the custom layout for medieval logic texts

## Useful commands

| Command | What it does |
|---------|-------------|
| `bundle exec jekyll serve` | Build and serve locally with live reload |
| `bundle exec jekyll build` | Build the site without serving (output in `_site/`) |
| `bundle install` | Install gems from `Gemfile` |
| `bundle update` | Update all gems to latest compatible versions |
| `bundle exec jekyll serve --drafts` | Include files in `_drafts/` folder |
| `bundle exec jekyll serve --port 5000` | Use a different port |

## Troubleshooting

- **"Could not find gem"**: Run `bundle install`
- **Layout not applied**: Check that `layout:` is set in the file's front matter, or that `_config.yml` has a `defaults` block
- **Changes not showing**: Restart the server if you changed `_config.yml`; for other files, just refresh the browser
- **Port in use**: Use `--port 5000` or kill the old process with `pkill -f jekyll`
