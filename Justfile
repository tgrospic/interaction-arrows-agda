# Commands for the interaction-arrow Agda development.
# Run `just` to list them. Override the compiler with `AGDA=/path/to/agda`.

set shell := ["bash", "-euo", "pipefail", "-c"]

export LC_ALL := "C.UTF-8"

agda := env_var_or_default("AGDA", "agda")

# List the available commands.
default:
    @just --list --unsorted

# Show the active Agda executable, version, directories, and registered libraries.
info:
    #!/usr/bin/env bash
    command -v {{agda}}
    {{agda}} --version
    echo "data: $({{agda}} --print-agda-data-dir)"
    app=$({{agda}} --print-agda-app-dir)
    echo "config: $app"
    echo "libraries:"
    found=0
    while IFS= read -r file; do
      [ -f "$file" ] || continue
      found=1
      printf "  %-28s %s\n" "$(sed -n 's/^name:[[:space:]]*//p' "$file")" "$file"
    done < "$app/libraries" 2>/dev/null || true
    [ "$found" -eq 1 ] || echo "  (none found)"

# Verify that Agda, the project, and its standard-library dependency are usable.
doctor:
    #!/usr/bin/env bash
    echo "locale: $LC_ALL"
    {{agda}} --version
    {{agda}} --only-scope-checking src/Game.agda
    echo "OK: Agda can load this project"

# Run the complete local and CI gate.
ci: doctor check-all

# Show the project requirement and every registered stdlib.
stdlib-info:
    #!/usr/bin/env bash
    echo "Agda:   $({{agda}} --version | head -1)"
    echo "Project: $(sed -n 's/^depend:[[:space:]]*//p' interaction-arrows.agda-lib)"
    app=$({{agda}} --print-agda-app-dir)
    echo "Registered:"
    found=0
    while IFS= read -r file; do
      [ -f "$file" ] || continue
      found=1
      printf "  %-28s %s\n" "$(sed -n 's/^name:[[:space:]]*//p' "$file")" "$file"
    done < "$app/libraries" 2>/dev/null || true
    [ "$found" -eq 1 ] || echo "  (none)"

# Register an existing standard-library manifest with Agda.
stdlib-register FILE:
    #!/usr/bin/env bash
    manifest=$(realpath "{{FILE}}")
    [ -f "$manifest" ] || { echo "not found: $manifest"; exit 1; }
    name=$(sed -n 's/^name:[[:space:]]*//p' "$manifest")
    [ -n "$name" ] || { echo "missing name in $manifest"; exit 1; }
    app=$({{agda}} --print-agda-app-dir)
    mkdir -p "$app"
    touch "$app/libraries"
    grep -qxF "$manifest" "$app/libraries" || printf '%s\n' "$manifest" >> "$app/libraries"
    echo "registered $name"

# Select a registered version for this project: `just stdlib-use 2.4`.
stdlib-use VERSION:
    #!/usr/bin/env bash
    version="{{VERSION}}"
    [[ "$version" =~ ^[0-9]+\.[0-9]+(\.[0-9]+)?$ ]] || { echo "invalid version: $version"; exit 1; }
    name="standard-library-$version"
    app=$({{agda}} --print-agda-app-dir)
    found=0
    while IFS= read -r file; do
      [ -f "$file" ] || continue
      [ "$(sed -n 's/^name:[[:space:]]*//p' "$file")" = "$name" ] && found=1
    done < "$app/libraries" 2>/dev/null || true
    [ "$found" -eq 1 ] || { echo "$name is not registered; install or register it first"; exit 1; }
    sed -i -E "s/^depend:.*/depend: $name/" interaction-arrows.agda-lib
    echo "project now uses $name"

# Clone, register, and select an upstream stdlib release in the user data folder.
stdlib-install VERSION:
    #!/usr/bin/env bash
    version="{{VERSION}}"
    [[ "$version" =~ ^[0-9]+\.[0-9]+(\.[0-9]+)?$ ]] || { echo "invalid version: $version"; exit 1; }
    base="${XDG_DATA_HOME:-$HOME/.local/share}/agda/libraries"
    target="$base/agda-stdlib-$version"
    mkdir -p "$base"
    if [ ! -e "$target" ]; then
      git clone --depth 1 --branch "v$version" \
        https://github.com/agda/agda-stdlib.git "$target"
    fi
    [ -f "$target/standard-library.agda-lib" ] || { echo "invalid installation: $target"; exit 1; }
    just stdlib-register "$target/standard-library.agda-lib"
    just stdlib-use "$version"
    echo "installed standard-library-$version in $target"

# Type-check one module: `just check src/BoolExample.agda`.
check FILE:
    {{agda}} "{{FILE}}"

# Type-check every module under src/ and print a compact summary.
check-all:
    #!/usr/bin/env bash
    log=$(mktemp)
    trap 'rm -f "$log"' EXIT
    mapfile -t files < <(find src -type f -name '*.agda' | sort)
    pass=0
    for file in "${files[@]}"; do
      if {{agda}} "$file" >"$log" 2>&1; then
        echo "PASS  $file"
        pass=$((pass + 1))
      else
        echo "FAIL  $file"
        sed 's/^/      /' "$log"
        exit 1
      fi
    done
    echo "$pass/${#files[@]} modules passed"

# Alias for `check-all`.
test: check-all

# Quickly scope-check one module without full type-checking.
scope FILE:
    {{agda}} --only-scope-checking "{{FILE}}"

# Scope-check every module under src/.
scope-all:
    #!/usr/bin/env bash
    mapfile -t files < <(find src -type f -name '*.agda' | sort)
    for file in "${files[@]}"; do
      echo "SCOPE $file"
      {{agda}} --only-scope-checking "$file"
    done

# Recheck a module without using cached interface files.
recheck FILE:
    {{agda}} --ignore-interfaces "{{FILE}}"

# Show module-level type-checking timings.
profile FILE:
    {{agda}} --profile=modules "{{FILE}}"

# Compile a module containing `main` through GHC into build/.
compile FILE:
    {{agda}} --compile --compile-dir=build "{{FILE}}"

# Generate browsable HTML for a module in html/.
html FILE:
    {{agda}} --html "{{FILE}}"
    @echo "generated html/$(basename "{{FILE}}" .agda).html"

# List cached Agda interface files.
interfaces:
    @find _build -type f -name '*.agdai' 2>/dev/null | sort || true

# Show module declarations alongside their source paths.
modules:
    @rg -n '^module ' src --glob '*.agda' | sort

# Remove this project's generated Agda interfaces.
clean:
    rm -rf _build
