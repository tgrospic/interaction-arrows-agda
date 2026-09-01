#!/usr/bin/env bash
# Clone every repo of Conal Elliott's that contains Agda, into external/.
#
# external/ is gitignored: none of his repos carries a LICENSE file, so this
# project links to his work and fetches it on demand rather than vendoring it.
#
# The repo list comes from scanning all 121 of his public repos for .agda and
# .lagda files, not from GitHub's "primary language" field, which misses the
# paper and talk repos where the Agda sits beside TeX.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
ext="$root/external"
libs="${XDG_CONFIG_HOME:-$HOME/.config}/agda/libraries"

# Repos he authored.
authored=(
  felix                            # category theory for denotational design
  paper-2021-language-derivatives  # Agda behind the language derivatives paper
  agda-cat-linear                  # linear map categories (needs agda-categories)
  felix-boolean                    # boolean structure layered on felix
  agda-play                        # miscellaneous experiments
  DependentTypesAtWork-exercises   # exercises from "Dependent Types at Work"
  nim                              # the game of Nim
  agda-puzzles                     # Tower of Hanoi
  equation-transfer                # equational properties through homomorphisms
  talk-2023-galilean-revolution    # talk sources, one literate module
  agda-latex                       # literate TeX scaffolding, depends on felix
)

# Forks he keeps. Upstream code, not his writing, so they are opt-in.
forks=(
  agda-categories                  # needed by agda-cat-linear
  cheshire                         # category theory library
  blag                             # blog framework with Agda posts
  agda-stdlib                      # the standard library itself
  jespercockx-agda-lecture-notes   # the lecture notes he recommends
)

clone() {
  if [ -d "$ext/$1/.git" ]; then echo "have    $1"
  else echo "clone   $1"; git clone -q --depth 1 "https://github.com/conal/$1.git" "$ext/$1"; fi
}

mkdir -p "$ext" "$(dirname "$libs")"
touch "$libs"

for r in "${authored[@]}"; do clone "$r"; done
if [ "${WITH_FORKS:-0}" = "1" ]; then
  for r in "${forks[@]}"; do clone "$r"; done
elif [ "${WITH_CATEGORIES:-0}" = "1" ]; then
  clone agda-categories
fi

# The repos without their own .agda-lib share one project root so their flat
# module names resolve. agda-play/DependentTypesAtWork is left out: it duplicates
# DependentTypesAtWork-exercises and would make those modules ambiguous.
cat > "$ext/conal-examples.agda-lib" <<'LIB'
name: conal-examples
depend: standard-library
include: nim agda-puzzles DependentTypesAtWork-exercises agda-play equation-transfer/src
LIB

# Register only libraries something else depends on, or that you would import.
# template.agda-lib is skipped deliberately: two repos ship one, both named
# "name-goes-here", and registering both collides.
for lib in "$ext"/conal-examples.agda-lib \
           "$ext"/felix/felix.agda-lib \
           "$ext"/felix-boolean/felix-boolean.agda-lib \
           "$ext"/agda-cat-linear/cat-linear.agda-lib \
           "$ext"/paper-2021-language-derivatives/ld.agda-lib \
           "$ext"/cheshire/cheshire.agda-lib \
           "$ext"/agda-categories/agda-categories.agda-lib; do
  [ -f "$lib" ] || continue
  grep -qxF "$lib" "$libs" || { echo "register $(basename "$lib")"; echo "$lib" >> "$libs"; }
done

echo
echo "Repos with their own template.agda-lib (talk-2023, agda-latex) are not"
echo "registered; check them by cd'ing in first:  cd external/agda-latex && agda src/All.lagda.tex"
