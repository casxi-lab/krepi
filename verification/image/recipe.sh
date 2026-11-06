# Shell functions for the RUN steps of the image recipe in this directory.
# Each step that needs them sources this file, which defines functions only.
# Every function fails, and with it the step, on any error.

# The pin at the jq path $1 of the tool manifest; fails when the field is
# missing or null.
pin() {
  jq --exit-status --raw-output "$1" /pins/toolchain.json
}

# The pin at the jq path $1 of the manifest's linux-aarch64 column.
host_pin() {
  pin ".hosts[\"linux-aarch64\"]$1"
}

# Downloads the HTTPS URL $2 to the file $1 and checks that its SHA-256 is
# $3.
fetch() {
  curl --proto '=https' --tlsv1.2 --fail --silent --show-error --location \
    --retry 5 --retry-all-errors --output "$1" "$2"
  check_sha256 "$1" "$3"
}

# Fails unless the file $1 has the SHA-256 $2.
check_sha256() {
  printf '%s  %s\n' "$2" "$1" | sha256sum --check --strict
}

# The SHA-256 of the file $1.
sha256_of() {
  local line
  line=$(sha256sum "$1")
  printf '%s\n' "${line%% *}"
}

# Fails unless the Git checkout $1 is at the commit $2.
at_commit() {
  local found
  found=$(git -C "$1" rev-parse HEAD)
  if [ "$found" != "$2" ]; then
    echo "$1 is at $found, not at the pinned commit $2" >&2
    return 1
  fi
}

# Fetches the commit $3 of the Git repository at the URL $2 into the new
# directory $1, checks it out and checks that it is at that commit.
fetch_commit() {
  git init --quiet "$1"
  git -C "$1" fetch --quiet --depth 1 "$2" "$3"
  git -C "$1" checkout --quiet --detach FETCH_HEAD
  at_commit "$1" "$3"
}

# Fails unless every submodule of the Git checkout $1, recursively, is
# checked out at the commit that its parent records; prints each as its path
# and commit, one per line.
submodule_commits() {
  local status line commit path
  status=$(git -C "$1" submodule status --recursive) || return 1
  while IFS= read -r line; do
    [ -n "$line" ] || continue
    case "$line" in
      ' '*) ;;
      *)
        echo "a submodule of $1 is not at its recorded commit: $line" >&2
        return 1
        ;;
    esac
    line=${line# }
    commit=${line%% *}
    path=${line#* }
    printf '%s %s\n' "${path%% (*}" "$commit"
  done <<<"$status"
}

# The license, copying, copyright and notice files at the top of the
# directory $1, one per line.
license_files() {
  find "$1" -maxdepth 1 -type f \( -iname 'licen[cs]e*' -o -iname 'copying*' \
    -o -iname 'copyright*' -o -iname 'notice*' \)
}

# Copies the license files at the top of the directory $1 to the directory
# $2, which it creates; fails when $1 has none.
copy_license_files() {
  local files file
  files=$(license_files "$1") || return 1
  if [ -z "$files" ]; then
    echo "$1 has no license file" >&2
    return 1
  fi
  mkdir -p "$2"
  while IFS= read -r file; do
    cp "$file" "$2/" || return 1
  done <<<"$files"
}

# Copies to the directory $3 the standard texts, from the directory $2, of
# the licenses that the SPDX expression $1 names: every one for an
# expression with AND, WITH or parentheses, and at least one for a choice
# between licenses. Fails when a needed text is missing.
standard_license_texts() {
  local id all=0 copied=0
  case "$1" in *'('* | *' AND '* | *' WITH '*) all=1 ;; esac
  mkdir -p "$3"
  for id in $(printf '%s\n' "$1" | tr '()/' '   '); do
    case "$id" in OR | AND | WITH) continue ;; esac
    if [ -f "$2/$id.txt" ]; then
      cp "$2/$id.txt" "$3/" || return 1
      copied=$((copied + 1))
    elif [ "$all" = 1 ]; then
      echo "there is no standard text of $id, which \`$1\` needs" >&2
      return 1
    fi
  done
  if [ "$copied" = 0 ]; then
    echo "there is no standard text of any license of \`$1\`" >&2
    return 1
  fi
}

# Collects the license texts of the crates that the package of the Cargo
# manifest $1 links when it is built for the target $2: the packages from
# registries and Git repositories that its normal and build dependencies
# reach, without development dependencies. Each crate gets a directory below
# $3 with the license files at the top of its package or, for a crate from a
# Git repository without any, at the top of its repository. A crate that
# ships no license file gets the standard texts of the licenses it declares,
# from the Rust toolchain, and a file PACKAGE that says so. Fails when the
# texts of a crate cannot be found. Lists each crate with its declared
# license in $3/index.txt. The crates must have been fetched for $2.
crate_notices() {
  local standard metadata crates name version source license dir authors out top
  standard="$(rustc --print sysroot)/share/doc/rust/licenses"
  metadata=$(cargo metadata --locked --offline --format-version 1 \
    --filter-platform "$2" --manifest-path "$1") || return 1
  crates=$(jq --raw-output '
      (.resolve.nodes
        | map({key: .id,
               value: [.deps[] | select(any(.dep_kinds[]; .kind != "dev")) | .pkg]})
        | from_entries) as $deps
      | ({seen: [.resolve.root], todo: [.resolve.root]}
         | until(.todo == [];
             .todo[0] as $id
             | .todo |= .[1:]
             | reduce $deps[$id][] as $dep (.;
                 if (.seen | index($dep)) then .
                 else .seen += [$dep] | .todo += [$dep] end))
         | .seen) as $linked
      | .packages[]
      | select(.source != null and (.id as $id | $linked | index($id)))
      | [.name, .version, .source, (.license // "none declared"),
         (.manifest_path | rtrimstr("/Cargo.toml")),
         (.authors | join(", ") | if . == "" then "none named" else . end)]
      | @tsv' <<<"$metadata" | sort) || return 1
  if [ -z "$crates" ]; then
    echo "$1 links no crate from a registry or a Git repository" >&2
    return 1
  fi
  mkdir -p "$3"
  while IFS=$'\t' read -r name version source license dir authors; do
    out="$3/$name-$version"
    printf '%s %s: %s\n' "$name" "$version" "$license" >>"$3/index.txt"
    if [ -n "$(license_files "$dir")" ]; then
      copy_license_files "$dir" "$out" || return 1
      continue
    fi
    if [ "${source%%+*}" = git ]; then
      top=$(git -C "$dir" rev-parse --show-toplevel) || return 1
      if [ -n "$(license_files "$top")" ]; then
        copy_license_files "$top" "$out" || return 1
        continue
      fi
    fi
    standard_license_texts "$license" "$standard" "$out" || return 1
    printf '%s %s from %s declares the license %s and ships no license file; the standard texts of its licenses are beside this file. Authors: %s.\n' \
      "$name" "$version" "$source" "$license" "$authors" >"$out/PACKAGE"
  done <<<"$crates"
}

# Collects the license texts of the packages of the current opam switch, one
# directory per package below $1, and lists each package with its declared
# license in $1/index.txt. The texts of a package are the license files that
# it installs into its documentation directory or, when it installs none,
# those at the top of its source, which `opam source` fetches and checks
# against the checksum in the pinned opam repository. A package without a
# source, such as a `base-` or `conf-` package or a compiler variant, holds
# no code and gets only its line. Fails when a package with a source has no
# license file.
opam_notices() {
  local prefix work packages name version license source
  prefix=$(opam var prefix) || return 1
  packages=$(opam list --installed --columns=name,version --short --separator=' ') || return 1
  if [ -z "$packages" ]; then
    echo "the opam switch has no package" >&2
    return 1
  fi
  work=$(mktemp -d) || return 1
  mkdir -p "$1"
  while read -r name version; do
    license=$(opam show --field=license "$name.$version" </dev/null) || return 1
    license=$(tr -d '"' <<<"$license")
    source=$(opam show --field=url.src: "$name.$version" </dev/null) || return 1
    if [ -d "$prefix/doc/$name" ] && [ -n "$(license_files "$prefix/doc/$name")" ]; then
      copy_license_files "$prefix/doc/$name" "$1/$name" || return 1
    elif [ -n "$source" ]; then
      opam source --dir "$work/$name" "$name.$version" </dev/null || return 1
      copy_license_files "$work/$name" "$1/$name" || return 1
    else
      printf '%s %s: %s; no source, so no code\n' "$name" "$version" \
        "${license:-none declared}" >>"$1/index.txt"
      continue
    fi
    printf '%s %s: %s\n' "$name" "$version" "${license:-none declared}" >>"$1/index.txt"
  done <<<"$packages"
  rm -rf "$work"
}

# Copies the license file of every package of the Lake lock $1, whose
# checkouts are below $2, to one directory per package below $3; fails when
# a package has none.
lake_notices() {
  local name
  for name in $(jq --raw-output '.packages[].name' "$1"); do
    copy_license_files "$2/$name" "$3/$name" || return 1
  done
}

# Fails unless every directory that the notice index $1 lists, as the first
# word of a line that is neither empty nor a comment, exists below the
# directory of the index and holds a file that is not empty.
check_notices() {
  local base dir rest missing=0
  base=$(dirname "$1")
  while read -r dir rest; do
    case "$dir" in '' | '#'*) continue ;; esac
    if [ -z "$(find "$base/$dir" -type f -size +0 -print -quit 2>/dev/null)" ]; then
      echo "the notice of $dir ($rest) is missing" >&2
      missing=1
    fi
  done <"$1"
  return "$missing"
}
