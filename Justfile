# Helper commands for this Agda project.
# Run `just` to list, `just <recipe> --help` is not a thing; see COMMANDS.md for the raw commands.

set shell := ["bash", "-euo", "pipefail", "-c"]

# Agda dies printing its own Unicode error messages without a UTF-8 locale.
export LC_ALL := "C.UTF-8"

agda := env_var_or_default("AGDA", "agda")
sources := "essay scratch"

# List available recipes.
default:
    @just --list --unsorted

# Which agda, which version, where its data and config live.
info:
    @echo "binary:   $(command -v {{agda}})"
    @{{agda}} --version
    @echo "data dir: $({{agda}} --print-agda-data-dir)"
    @echo "app dir:  $({{agda}} --print-agda-app-dir)"
    @echo "libraries:"
    @sed 's/^/  /' ~/.config/agda/libraries 2>/dev/null || echo "  (none registered)"

# Check the install is usable: data dir writable, stdlib registered, locale sane.
doctor:
    #!/usr/bin/env bash
    set -uo pipefail
    d=$({{agda}} --print-agda-data-dir)
    prim="$d/lib/prim"
    n=$(find "$prim" -name '*.agdai' 2>/dev/null | wc -l)
    if [ -w "$prim" ]; then
      echo "ok    prim writable: $prim"
    elif [ "$n" -gt 0 ]; then
      echo "ok    prim read-only but has $n prebuilt interfaces: $prim"
    else
      echo "FAIL  prim read-only with no prebuilt interfaces: $prim"
      echo "      every load will try to create $prim/_build and be denied."
      echo "      fix: mkdir -p ~/.local/share/agda && export Agda_datadir=\$HOME/.local/share/agda && agda --setup"
    fi
    if grep -q . ~/.config/agda/libraries 2>/dev/null
      then echo "ok    $(grep -c . ~/.config/agda/libraries) librar(y/ies) registered"
      else echo "FAIL  none registered; run 'just setup-stdlib'"; fi
    echo "ok    locale $LC_ALL"

# Register the standard library (autodetects the Debian and Arch paths).
setup-stdlib:
    #!/usr/bin/env bash
    set -euo pipefail
    mkdir -p ~/.config/agda
    for p in /usr/share/agda-stdlib/standard-library.agda-lib \
             /usr/share/agda/lib/standard-library.agda-lib; do
      if [ -f "$p" ]; then
        grep -qxF "$p" ~/.config/agda/libraries 2>/dev/null || echo "$p" >> ~/.config/agda/libraries
        echo "registered $p"
      fi
    done
    grep -qx standard-library ~/.config/agda/defaults 2>/dev/null || echo standard-library >> ~/.config/agda/defaults

# Type-check one module.  just check scratch/pico.agda
check FILE:
    {{agda}} "{{FILE}}"

# Type-check every module, with a pass/fail summary.
check-all:
    #!/usr/bin/env bash
    set -uo pipefail
    if {{agda}} --help 2>&1 | grep -q -- '--build-library'; then
      exec {{agda}} --build-library
    fi
    pass=0; fail=0
    for f in $(find {{sources}} -name '*.agda' | sort); do
      if {{agda}} "$f" >/tmp/agda-check.log 2>&1; then
        echo "PASS  $f"; pass=$((pass+1))
      else
        echo "FAIL  $f"; grep -v '^Checking' /tmp/agda-check.log | grep -v '^$' | head -3 | sed 's/^/        /'
        fail=$((fail+1))
      fi
    done
    echo "--- $pass pass / $fail fail ---"
    [ "$fail" -eq 0 ]

# Scope-check only: fast structural pass over one module.
scope FILE:
    {{agda}} --only-scope-checking "{{FILE}}"

# Re-check from scratch, ignoring cached interfaces.
recheck FILE:
    {{agda}} --ignore-interfaces "{{FILE}}"

# Where time goes when a module is slow to check.
profile FILE:
    {{agda}} --profile=modules "{{FILE}}"

# Compile a module with a `main` to an executable via GHC.
compile FILE:
    {{agda}} --compile --compile-dir=build "{{FILE}}"

# Render a module and its dependencies to clickable HTML in html/.
html FILE:
    {{agda}} --html "{{FILE}}"
    @echo "open html/$(basename "{{FILE}}" .agda).html"

# Which modules currently have interfaces, meaning they checked clean.
ifaces:
    @find _build -name '*.agdai' 2>/dev/null | sed 's|_build/||' | sort || echo "(nothing built)"

# Audit module declarations against file paths.  A mismatch is a hard error in Agda.
modules:
    @grep -rn '^module' --include=*.agda {{sources}} | sed 's/:[0-9]*:module/  ->/' | sort

# Clone Conal's Agda repos into external/ and register the library ones.
fetch:
    ./scripts/fetch-conal.sh

# Same, plus the agda-categories fork that agda-cat-linear needs.
fetch-all:
    WITH_CATEGORIES=1 ./scripts/fetch-conal.sh

# Type-check Conal's felix library (the cd matters: include set comes from cwd).
felix:
    cd external/felix && {{agda}} src/Felix/All.agda

# Type-check felix-boolean, which depends on felix being registered.
felix-boolean:
    cd external/felix-boolean && {{agda}} src/Felix/Boolean/All.agda

# File and line counts per repo in the fetched corpus.
corpus:
    #!/usr/bin/env bash
    set -uo pipefail
    cd external 2>/dev/null || { echo "nothing fetched; run 'just fetch'"; exit 1; }
    printf "%-32s %6s %8s  %s\n" repo files lines note
    tf=0; tl=0
    for d in */; do
      r=${d%/}
      fs=$(find "$r" \( -name '*.agda' -o -name '*.lagda*' \))
      [ -n "$fs" ] || continue
      n=$(echo "$fs" | wc -l); l=$(cat $fs | wc -l)
      case "$r" in
        agda-categories|agda-stdlib|cheshire|blag|jespercockx-agda-lecture-notes) note="fork, not counted" ;;
        *) note=""; tf=$((tf+n)); tl=$((tl+l)) ;;
      esac
      printf "%-32s %6s %8s  %s\n" "$r" "$n" "$l" "$note"
    done
    printf "%-32s %6s %8s  %s\n" "TOTAL (authored)" "$tf" "$tl" ""

# Remove this project's interface files.
clean:
    rm -rf _build

# Also remove interfaces built inside the fetched repos.
clean-all: clean
    -find external -name _build -type d -prune -exec rm -rf {} + 2>/dev/null
