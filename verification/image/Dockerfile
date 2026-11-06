# The run image of the proof tools, for linux-aarch64: the Lean toolchain,
# the Aeneas Lean library with Mathlib built, Aeneas and Charon built from
# source, Charon's Rust nightly with the standard library for
# aarch64-unknown-none, and bubblewrap. The source trees and the opam build
# tree stay in the build stages.
#
# Every version comes from verification/toolchain.json. The build expects
# three contexts: the default context is the `verification/` directory of
# the repository, and the named contexts `aeneas-src` and `charon-src` are Git
# checkouts of the pinned Aeneas and Charon commits, Charon with its
# submodules, which `cargo xtask formal toolchain-check` has checked against
# the manifest. From the repository root:
#
#   docker build --file verification/image/Dockerfile \
#     --build-context aeneas-src=<Aeneas checkout> \
#     --build-context charon-src=<Charon checkout> verification
#
# The steps check every archive and binary that they download against its
# pinned SHA-256 and every Git checkout against its pinned commit, install
# the Rust nightly without letting rustup update itself, check the channel
# manifest and the commit of the installed rustc, check the patch and the
# Lake lock of the Aeneas Lean library against their pinned SHA-256 and
# Mathlib commit, check the opam switch against its pinned export once that
# is pinned, and fail when a third-party notice is missing. Two downloads
# have no pin of their own: Cargo checks the crates against the checksums of
# Charon's Cargo.lock, and `lake exe cache get` takes Mathlib's build cache,
# with its `leantar` tool, from Mathlib's cache service by the pinned Lake
# lock. The image holds the versions it observed in
# /opt/krepi-formal/versions.json.

ARG BASE=ubuntu:noble-20261024.1@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852

# Build tools and the pins, shared by the build stages.
FROM ${BASE} AS base
SHELL ["/bin/bash", "-euo", "pipefail", "-c"]
ENV DEBIAN_FRONTEND=noninteractive LANG=C.UTF-8 LC_ALL=C.UTF-8
RUN apt-get update; \
    apt-get install --yes --no-install-recommends \
      bzip2 ca-certificates curl g++ gcc git jq libc6-dev m4 make patch \
      pkgconf unzip xz-utils zstd; \
    rm -rf /var/lib/apt/lists/*
COPY toolchain.json image/recipe.sh /pins/
COPY tooling/ /pins/tooling/
RUN source /pins/recipe.sh; \
    prefix=$(host_pin .prefix); \
    if [ "$prefix" != /opt/krepi-formal ]; then \
      echo "the manifest's linux-aarch64 prefix is $prefix, not /opt/krepi-formal" >&2; exit 1; \
    fi

# The Aeneas sources with the patch applied, after checking the commit, the
# patch and the Lake lock.
FROM base AS aeneas-source
COPY --from=aeneas-src / /src/aeneas
RUN source /pins/recipe.sh; \
    commit=$(pin .aeneas.commit); \
    at_commit /src/aeneas "$commit"; \
    patch=$(pin .aeneas.patch); \
    patch=/pins/${patch#verification/}; \
    patch_sha256=$(pin .aeneas.patch_sha256); \
    check_sha256 "$patch" "$patch_sha256"; \
    git -C /src/aeneas apply --check "$patch"; \
    git -C /src/aeneas apply "$patch"; \
    lock=/src/aeneas/backends/lean/lake-manifest.json; \
    lock_sha256=$(pin .aeneas.lake_manifest_sha256); \
    check_sha256 "$lock" "$lock_sha256"; \
    mathlib=$(pin .aeneas.mathlib_commit); \
    locked=$(jq --exit-status --raw-output \
      '[.packages[] | select(.name == "mathlib")] | if length == 1 then .[0].rev else null end' "$lock"); \
    if [ "$locked" != "$mathlib" ]; then \
      echo "the Lake lock pins Mathlib $locked, not $mathlib" >&2; exit 1; \
    fi; \
    mkdir -p /facts; \
    jq --null-input --arg commit "$commit" --arg patch "$(sha256_of "$patch")" \
      '{aeneas: {commit: $commit, patch_sha256: $patch}}' >/facts/aeneas-source.json

# The Lean toolchain, with lean, lake and leanchecker.
FROM base AS lean
RUN source /pins/recipe.sh; \
    url=$(host_pin .lean.url); \
    sha256=$(host_pin .lean.sha256); \
    version=$(pin .lean.version); \
    commit=$(pin .lean.commit); \
    fetch /tmp/lean.tar.zst "$url" "$sha256"; \
    observed_sha256=$(sha256_of /tmp/lean.tar.zst); \
    mkdir -p /opt/krepi-formal/lean; \
    tar --zstd --extract --file /tmp/lean.tar.zst --directory /opt/krepi-formal/lean \
      --strip-components 1 --no-same-owner; \
    rm /tmp/lean.tar.zst; \
    line=$(/opt/krepi-formal/lean/bin/lean --version); \
    echo "$line"; \
    observed_version=$(sed -n 's/^Lean (version \([^,]*\),.*/\1/p' <<<"$line"); \
    observed_commit=$(sed -n 's/.*, commit \([0-9a-f]*\),.*/\1/p' <<<"$line"); \
    if [ "$observed_version" != "$version" ] || [ "$observed_commit" != "$commit" ]; then \
      echo "lean reports $line; the manifest pins $version at $commit" >&2; exit 1; \
    fi; \
    chmod -R a-w /opt/krepi-formal/lean; \
    mkdir -p /facts; \
    jq --null-input --arg version "$observed_version" --arg commit "$observed_commit" \
      --arg sha256 "$observed_sha256" \
      '{lean: {version: $version, commit: $commit, sha256: $sha256}}' >/facts/lean.json

# rustup and Charon's Rust nightly.
FROM base AS rust-toolchain
ENV RUSTUP_HOME=/opt/krepi-formal/rustup CARGO_HOME=/opt/krepi-formal/cargo
ENV PATH=/opt/krepi-formal/cargo/bin:$PATH
RUN source /pins/recipe.sh; \
    url=$(host_pin .rustup_init.url); \
    sha256=$(host_pin .rustup_init.sha256); \
    toolchain=$(pin .rust.toolchain); \
    commit=$(pin .rust.rustc_commit); \
    components=$(pin '.rust.components | join(",")'); \
    targets=$(pin '.rust.targets | join(",")'); \
    manifest_url=$(pin .rust.manifest_url); \
    manifest_sha256=$(pin .rust.manifest_sha256); \
    rustup_version=$(pin .rust.rustup); \
    rustup_url=$(pin .rust.rustup_source_url); \
    rustup_commit=$(pin .rust.rustup_commit); \
    fetch /tmp/rustup-init "$url" "$sha256"; \
    rustup_init_sha256=$(sha256_of /tmp/rustup-init); \
    chmod 0755 /tmp/rustup-init; \
    /tmp/rustup-init -y --no-modify-path --profile minimal --default-toolchain none; \
    rm /tmp/rustup-init; \
    rustup set auto-self-update disable; \
    line=$(rustup --version 2>/dev/null | sed -n 1p); \
    echo "$line"; \
    observed_rustup=$(sed -n 's/^rustup \([^ ]*\) (\([0-9a-f]*\) .*/\1/p' <<<"$line"); \
    observed_rustup_commit=$(sed -n 's/^rustup \([^ ]*\) (\([0-9a-f]*\) .*/\2/p' <<<"$line"); \
    if [ "$observed_rustup" != "$rustup_version" ] || [ -z "$observed_rustup_commit" ] \
        || [ "${rustup_commit#"$observed_rustup_commit"}" = "$rustup_commit" ]; then \
      echo "rustup reports $line; the manifest pins $rustup_version at $rustup_commit" >&2; exit 1; \
    fi; \
    fetch_commit /tmp/rustup-src "$rustup_url" "$rustup_commit"; \
    copy_license_files /tmp/rustup-src /notices/rustup; \
    rm -rf /tmp/rustup-src; \
    rustup toolchain install "$toolchain" --profile minimal --component "$components" \
      --target "$targets" --no-self-update; \
    fetch /tmp/channel-rust.toml "$manifest_url" "$manifest_sha256"; \
    named=$(awk '/^\[pkg\.rustc\]$/ { inside = 1; next } /^\[/ { inside = 0 } \
      inside && $1 == "git_commit_hash" { gsub(/"/, "", $3); print $3 }' /tmp/channel-rust.toml); \
    rm /tmp/channel-rust.toml; \
    observed_commit=$(rustc "+$toolchain" -vV | sed -n 's/^commit-hash: //p'); \
    if [ "$named" != "$commit" ] || [ "$observed_commit" != "$commit" ]; then \
      echo "the channel manifest names rustc $named and rustc reports $observed_commit; the manifest pins $commit" >&2; \
      exit 1; \
    fi; \
    installed_components=$(rustup component list --installed --toolchain "$toolchain"); \
    installed_targets=$(rustup target list --installed --toolchain "$toolchain"); \
    mkdir -p /notices/rust; \
    cp -R "$RUSTUP_HOME/toolchains/$toolchain-aarch64-unknown-linux-gnu/share/doc/." /notices/rust/; \
    chmod -R a-w "$RUSTUP_HOME" "$CARGO_HOME"; \
    mkdir -p /facts; \
    jq --null-input --arg toolchain "$toolchain" --arg commit "$observed_commit" \
      --arg manifest "$manifest_sha256" --arg rustup "$observed_rustup" \
      --arg rustup_commit "$rustup_commit" --arg rustup_init "$rustup_init_sha256" \
      --arg components "$installed_components" --arg targets "$installed_targets" \
      '{rust: {toolchain: $toolchain, rustc_commit: $commit, manifest_sha256: $manifest, \
               rustup: $rustup, rustup_commit: $rustup_commit, \
               rustup_init_sha256: $rustup_init, \
               components: ($components | split("\n")), \
               targets: ($targets | split("\n"))}}' >/facts/rust.json

# Charon and its driver, built with the pinned nightly and Cargo lock.
FROM rust-toolchain AS charon-build
COPY --from=charon-src / /src/charon
RUN source /pins/recipe.sh; \
    commit=$(pin .charon.commit); \
    toolchain=$(pin .rust.toolchain); \
    at_commit /src/charon "$commit"; \
    submodules=$(submodule_commits /src/charon); \
    echo "submodules: $submodules"; \
    export CARGO_HOME=/build/cargo RUSTUP_TOOLCHAIN="$toolchain" RUSTUP_AUTO_INSTALL=0; \
    export CHARON_GIT_COMMIT="$commit" CARGO_PROFILE_RELEASE_DEBUG=true; \
    host=$(rustc -vV | sed -n 's/^host: //p'); \
    cargo build --release --locked --manifest-path /src/charon/charon/Cargo.toml; \
    install -d /opt/krepi-formal/bin; \
    install -m 0555 /src/charon/charon/target/release/charon \
      /src/charon/charon/target/release/charon-driver /opt/krepi-formal/bin/; \
    version=$(/opt/krepi-formal/bin/charon version); \
    echo "charon $version"; \
    copy_license_files /src/charon /notices/charon; \
    while read -r path sub; do \
      if [ -n "$path" ]; then copy_license_files "/src/charon/$path" "/notices/charon/$path"; fi; \
    done <<<"$submodules"; \
    cargo fetch --locked --target "$host" --manifest-path /src/charon/charon/Cargo.toml; \
    crate_notices /src/charon/charon/Cargo.toml "$host" /notices/charon-crates; \
    rm -rf /src/charon/charon/target /build/cargo; \
    jq --null-input --arg commit "$commit" --arg version "$version" \
      --arg submodules "$submodules" \
      '{charon: {commit: $commit, version: $version, \
                 submodules: ($submodules | split("\n") | map(select(length > 0) | split(" ") \
                              | {(.[0]): .[1]}) | add // {})}}' >/facts/charon.json

# GMP, built from the pinned source archive for the OCaml switch and the
# image.
FROM base AS gmp
RUN source /pins/recipe.sh; \
    url=$(pin .gmp.url); \
    sha256=$(pin .gmp.sha256); \
    version=$(pin .gmp.version); \
    mkdir -p /build/gmp /notices/gmp /out/lib; \
    fetch "/notices/gmp/gmp-$version.tar.xz" "$url" "$sha256"; \
    tar --extract --file "/notices/gmp/gmp-$version.tar.xz" --directory /build/gmp \
      --strip-components 1 --no-same-owner; \
    cd /build/gmp; \
    ./configure --prefix=/usr/local --enable-shared --disable-static; \
    make -j"$(nproc)"; \
    make install; \
    ldconfig; \
    cp COPYING COPYING.LESSERv3 COPYINGv2 COPYINGv3 /notices/gmp/; \
    cp -P /usr/local/lib/libgmp.so* /out/lib/; \
    cd /; \
    rm -rf /build/gmp; \
    observed_version=$(pkg-config --modversion gmp); \
    mkdir -p /facts; \
    jq --null-input --arg version "$observed_version" \
      --arg sha256 "$(sha256_of "/notices/gmp/gmp-$version.tar.xz")" \
      '{gmp: {version: $version, sha256: $sha256}}' >/facts/gmp.json

# The OCaml switch from the pinned opam and opam repository, and the patched
# Aeneas binary.
FROM gmp AS aeneas-build
ENV OPAMROOT=/build/opam OPAMYES=1 OPAMROOTISOK=1 OPAMCOLOR=never
RUN source /pins/recipe.sh; \
    url=$(host_pin .opam.url); \
    sha256=$(host_pin .opam.sha256); \
    version=$(pin .opam.version); \
    repository_url=$(pin .opam.repository_url); \
    repository_commit=$(pin .opam.repository_commit); \
    compiler=$(pin .opam.compiler); \
    fetch /usr/local/bin/opam "$url" "$sha256"; \
    mkdir -p /facts; \
    sha256_of /usr/local/bin/opam >/facts/opam.sha256; \
    chmod 0755 /usr/local/bin/opam; \
    observed_version=$(opam --version); \
    if [ "$observed_version" != "$version" ]; then \
      echo "opam reports $observed_version; the manifest pins $version" >&2; exit 1; \
    fi; \
    fetch_commit /build/opam-repository "$repository_url" "$repository_commit"; \
    opam init --bare --no-setup --no-opamrc --disable-sandboxing \
      pinned "git+file:///build/opam-repository#$repository_commit"; \
    opam option --global depext=false; \
    opam switch create krepi "$compiler"
COPY --from=aeneas-source /src/aeneas /src/aeneas
COPY --from=charon-src / /src/aeneas/charon
RUN source /pins/recipe.sh; \
    commit=$(pin .aeneas.commit); \
    charon=$(pin .charon.commit); \
    patch_sha256=$(pin .aeneas.patch_sha256); \
    at_commit /src/aeneas/charon "$charon"; \
    opam install --deps-only /src/aeneas/charon /src/aeneas/src; \
    cd /src/aeneas/src; \
    AENEAS_VERSION="${commit:0:7}+patch-${patch_sha256:0:8}" \
      opam exec -- dune build --profile release main.exe; \
    install -D -m 0555 _build/default/main.exe /opt/krepi-formal/bin/aeneas; \
    cd /; \
    aeneas_version=$(/opt/krepi-formal/bin/aeneas -version); \
    echo "aeneas $aeneas_version"; \
    ocaml_version=$(opam exec -- ocamlc -version); \
    opam switch export --full /facts/opam-switch.export; \
    export_sha256=$(sha256_of /facts/opam-switch.export); \
    pinned_export=$(host_pin '.switch_export_sha256 // ""'); \
    echo "opam switch export --full: SHA-256 $export_sha256"; \
    if [ -z "$pinned_export" ]; then \
      echo "the manifest pins no linux-aarch64 switch export yet"; \
    elif [ "$export_sha256" != "$pinned_export" ]; then \
      cat /facts/opam-switch.export; \
      echo "the switch export has SHA-256 $export_sha256; the manifest pins $pinned_export" >&2; \
      exit 1; \
    fi; \
    copy_license_files /src/aeneas /notices/aeneas; \
    opam_notices /notices/opam; \
    repository=$(git -C /build/opam-repository rev-parse HEAD); \
    jq --null-input --arg aeneas "$aeneas_version" --arg opam "$(opam --version)" \
      --arg opam_sha256 "$(cat /facts/opam.sha256)" \
      --arg repository "$repository" --arg ocaml "$ocaml_version" \
      --arg export "$export_sha256" \
      '{aeneas: {version: $aeneas}, \
        opam: {version: $opam, sha256: $opam_sha256, repository_commit: $repository, \
               ocaml: $ocaml, switch_export_sha256: $export}}' >/facts/aeneas-build.json; \
    rm /facts/opam.sha256

# The Aeneas Lean library, built with Mathlib from the Mathlib cache.
FROM lean AS backend
COPY --from=aeneas-source /src/aeneas/backends/lean /opt/krepi-formal/backend
WORKDIR /opt/krepi-formal/backend
ENV PATH=/opt/krepi-formal/lean/bin:$PATH
RUN source /pins/recipe.sh; \
    lock_sha256=$(pin .aeneas.lake_manifest_sha256); \
    mathlib=$(pin .aeneas.mathlib_commit); \
    lake exe cache get; \
    lake build Aeneas; \
    rm -rf /root/.cache; \
    check_sha256 lake-manifest.json "$lock_sha256"; \
    at_commit .lake/packages/mathlib "$mathlib"; \
    lake_notices lake-manifest.json .lake/packages /notices/lean-packages; \
    chmod -R a-w /opt/krepi-formal/backend; \
    mkdir -p /stage; \
    mv .lake/packages/mathlib /stage/mathlib; \
    mv /opt/krepi-formal/backend /stage/backend; \
    jq --null-input --arg lock "$(sha256_of /stage/backend/lake-manifest.json)" \
      --arg mathlib "$(git -C /stage/mathlib rev-parse HEAD)" \
      '{aeneas: {lake_manifest_sha256: $lock, mathlib_commit: $mathlib}}' >/facts/backend.json
WORKDIR /

# The system packages of the image.
FROM ${BASE} AS runtime
SHELL ["/bin/bash", "-euo", "pipefail", "-c"]
ENV DEBIAN_FRONTEND=noninteractive LANG=C.UTF-8 LC_ALL=C.UTF-8
RUN apt-get update; \
    apt-get install --yes --no-install-recommends bubblewrap ca-certificates git time; \
    rm -rf /var/lib/apt/lists/*

FROM runtime AS runtime-versions
RUN mkdir -p /facts; \
    dpkg-query --show --showformat '${Package}\t${Version}\n' bubblewrap git >/facts/apt.tsv

# The third-party notices and the GMP source archive.
FROM base AS notices
COPY image/notices.txt /opt/krepi-formal/notices/README
COPY tooling/ /opt/krepi-formal/notices/aeneas-patch/
COPY --from=lean /opt/krepi-formal/lean/LICENSE /opt/krepi-formal/notices/lean/
COPY --from=lean /opt/krepi-formal/lean/LICENSES /opt/krepi-formal/notices/lean/LICENSES
COPY --from=rust-toolchain /notices/ /opt/krepi-formal/notices/
COPY --from=charon-build /notices/ /opt/krepi-formal/notices/
COPY --from=gmp /notices/ /opt/krepi-formal/notices/
COPY --from=aeneas-build /notices/ /opt/krepi-formal/notices/
COPY --from=backend /notices/ /opt/krepi-formal/notices/
COPY --from=runtime /usr/share/doc/bubblewrap/copyright /opt/krepi-formal/notices/bubblewrap/
COPY --from=runtime /usr/share/doc/git/copyright /opt/krepi-formal/notices/git/
RUN source /pins/recipe.sh; \
    check_notices /opt/krepi-formal/notices/README; \
    chmod -R a-w /opt/krepi-formal/notices

# The version manifest, from what the build stages observed.
FROM base AS versions
ARG BASE
COPY --from=aeneas-source /facts/ /facts/
COPY --from=lean /facts/ /facts/
COPY --from=charon-build /facts/ /facts/
COPY --from=aeneas-build /facts/ /facts/
COPY --from=backend /facts/ /facts/
COPY --from=runtime-versions /facts/ /facts/
RUN jq --raw-input --slurp \
      'split("\n") | map(select(length > 0) | split("\t") | {(.[0]): .[1]}) | add | {apt: .}' \
      /facts/apt.tsv >/facts/apt.json; \
    mkdir -p /out; \
    jq --slurp --arg base "$BASE" \
      'reduce .[] as $facts ({schema: 1, base_image: $base}; . * $facts)' \
      /facts/*.json >/out/versions.json; \
    cp /facts/opam-switch.export /out/; \
    chmod a-w /out/*; \
    cat /out/versions.json

# The image.
FROM runtime AS image
ARG BASE
ARG REVISION=unknown
LABEL org.opencontainers.image.source="https://github.com/casxi-lab/krepi" \
      org.opencontainers.image.revision="$REVISION" \
      org.opencontainers.image.base.name="$BASE" \
      org.opencontainers.image.description="The pinned proof tools of krepi"
COPY --from=gmp /out/lib/ /usr/local/lib/
RUN ldconfig
COPY --from=lean /opt/krepi-formal/lean /opt/krepi-formal/lean
COPY --from=rust-toolchain /opt/krepi-formal/rustup /opt/krepi-formal/rustup
COPY --from=rust-toolchain /opt/krepi-formal/cargo /opt/krepi-formal/cargo
COPY --from=charon-build /opt/krepi-formal/bin/ /opt/krepi-formal/bin/
COPY --from=aeneas-build /opt/krepi-formal/bin/aeneas /opt/krepi-formal/bin/aeneas
COPY --from=backend /stage/backend /opt/krepi-formal/backend
COPY --from=backend /stage/mathlib /opt/krepi-formal/backend/.lake/packages/mathlib
COPY --from=notices /opt/krepi-formal/notices /opt/krepi-formal/notices
COPY --from=versions /out/ /opt/krepi-formal/
ENV RUSTUP_HOME=/opt/krepi-formal/rustup CARGO_HOME=/opt/krepi-formal/cargo
ENV PATH=/opt/krepi-formal/lean/bin:/opt/krepi-formal/bin:/opt/krepi-formal/cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
