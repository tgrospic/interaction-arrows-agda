# Useful commands

Everything here was run against this repo. Where a command only works on one Agda version, it says so. This machine runs Agda 2.6.4.3 with standard-library 2.1; the Arch box runs 2.8.0 with 2.4.

## Setup

Register the standard library. Agda finds libraries through a registry file, not a search path.

```bash
mkdir -p ~/.config/agda
echo /usr/share/agda-stdlib/standard-library.agda-lib >> ~/.config/agda/libraries   # Debian
echo /usr/share/agda/lib/standard-library.agda-lib    >> ~/.config/agda/libraries   # Arch
echo standard-library > ~/.config/agda/defaults
```

Fix the Arch data directory, which is root-owned and breaks interface writing. The binary carries its own data files, so no copying and no sudo.

```bash
mkdir -p ~/.local/share/agda
export Agda_datadir=$HOME/.local/share/agda
agda --setup                    # 2.8.0 only, and required: an empty dir is skipped otherwise
agda --print-agda-data-dir      # expect ~/.local/share/agda
```

Make that variable visible to a desktop-launched editor. `~/.profile` is not reliably read by systemd user sessions.

```bash
mkdir -p ~/.config/environment.d
printf 'Agda_datadir=%s/.local/share/agda\n' "$HOME" > ~/.config/environment.d/10-agda.conf
```

Fetch Conal's corpus into the gitignored `external/`.

```bash
./scripts/fetch-conal.sh
WITH_CATEGORIES=1 ./scripts/fetch-conal.sh    # also the agda-categories fork
```

## Checking

Always export a UTF-8 locale first, or Agda dies printing its own error messages with
`commitBuffer: invalid argument (cannot encode character '\8801')`.

```bash
export LC_ALL=C.UTF-8
```

One module. Interfaces land in `_build/<version>/agda/`.

```bash
agda scratch/pico.agda
```

The whole project in one command, on 2.7 and later. Walks every include root in the nearest `.agda-lib`.

```bash
agda --build-library
agda --build-library --only-scope-checking     # fast structural pass
```

The same thing on 2.6.x, which has no `--build-library`.

```bash
for f in $(find essay scratch -name '*.agda' | sort); do
  agda "$f" >/tmp/o.log 2>&1 \
    && echo "PASS  $f" \
    || { echo "FAIL  $f"; grep -v '^Checking' /tmp/o.log | grep -v '^$' | head -3; }
done
```

Check one of Conal's libraries. Note the `cd`: Agda takes its include set from the current
working directory, not from the file being checked, so this fails from the repo root.

```bash
cd external/felix        && agda src/Felix/All.agda
cd external/felix-boolean && agda src/Felix/Boolean/All.agda
```

## Inspecting

```bash
agda --version
agda --print-agda-data-dir      # where prim lives
agda --print-agda-app-dir       # where libraries/defaults live
agda --help | grep -i build     # confirm a flag exists on this version
```

Which modules have interfaces, meaning they checked successfully:

```bash
find _build -name '*.agdai' | sed 's|_build/||' | sort
```

Module declarations against their paths. A mismatch is a hard error, not a warning.

```bash
grep -rn '^module' --include=*.agda essay scratch | sed 's/:[0-9]*:module/  ->/'
```

Corpus line counts:

```bash
cd external
for r in */; do
  fs=$(find "${r%/}" \( -name '*.agda' -o -name '*.lagda*' \))
  echo "${r%/}: $(echo "$fs" | wc -l) files $(cat $fs | wc -l) lines"
done
```

## Compiling to an executable

Separate from type-checking, and per-module rather than per-project: point it at a module with
`main` and it compiles that module's dependency cone through GHC.

```bash
agda --compile Foo.agda
agda --compile --compile-dir=build Foo.agda
agda --js Foo.agda
```

## Cleaning

```bash
rm -rf _build                                    # this project's interfaces
find external -name _build -type d -prune -exec rm -rf {} +   # the clones' interfaces
```

## Editor

VS Code, `banacorn.agda-mode`. There is nothing to configure for the project itself: Agda walks
up from whatever file you load, finds `agda-collab.agda-lib`, and applies its include roots and
dependencies.

| Keys | Does |
| --- | --- |
| `C-c C-l` | load |
| `\` | unicode input, for example `\bN` gives `ℕ`, `\uplus` gives `⊎` |
| `C-c C-,` | goal type and context |
| `C-c C-.` | goal type, context and inferred term |
| `C-c C-SPC` | give |
| `C-c C-r` | refine |
| `C-c C-c` | case split |
| `C-c C-n` | compute normal form |
| `C-c C-d` | infer type |
| `C-c C-?` | show all goals |
| `C-c C-f` / `C-c C-b` | next / previous goal |
| `C-c C-x C-c` | compile |
| `C-c C-x C-r` | quit and restart, needed after editing the `.agda-lib` |

The project config is cached per session, so a plain reload will not pick up a changed
`include:` or `depend:`. If a chord does nothing, the Vim extension is eating it.
