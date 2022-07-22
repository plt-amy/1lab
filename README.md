[![Discord](https://img.shields.io/discord/914172963157323776?label=Discord&logo=discord)](https://discord.gg/NvXkUVYcxV)
[![Build 1Lab](https://github.com/plt-amy/cubical-1lab/actions/workflows/build.yml/badge.svg)](https://github.com/plt-amy/cubical-1lab/actions/workflows/build.yml)

# [1Lab](https://cubical.1lab.dev)

A formalised, cross-linked reference resource for mathematics done in
Homotopy Type Theory. Unlike the HoTT book, the 1lab is not a “linear”
resource: Concepts are presented as a directed graph, with links
indicating dependencies.

# Building

Here's how you can build --- and work on --- the web parts of the 1lab.

## Using Docker

An Arch Linux-based Docker container is provided which contains all the
dependencies necessary for building the 1lab, including the font files
required for a complete deployment. Since this container is on the
registry, we can do a one-line build of the 1Lab as follows:

```bash
% docker run -it -v $PWD:/workspace docker.io/pltamy/1lab:latest /bin/sh -i
$ 1lab-shake all -j       # build everything
$ sh support/make-site.sh # copy everything into place
```

After this, the directory `_build/site` will have everything in place
for use as the HTTP root of a static site to serve the 1Lab, for example
using the Python distribution that the container ships with:

```bash
$ python -m http.server --directory _build/site
```

## Using Nix

If you run NixOS, or have the Nix package manager installed, you can use
the provided `default.nix` file to build a complete, reproducible
deployment of the 1Lab. This has the benefit of also providing
`nix-shell` support for immediately setting up an environment for
development which supports compilation of the HTML and SVG files, in
addition to the Agda.

You can then use Nix to compile the project as usual. As a quick point
of reference, `nix build` will type-check and compile the entire thing,
and copy the necessary assets (TeX Gyre Pagella and KaTeX css/fonts) to
the right locations. The result will be linked as `./result`, which can
then be used to serve a website:

```bash
$ nix-build
$ python -m http.server --directory result
```

For interactive development, keep in mind that the `buildInputs` to
`default.nix` _don't_ include Stack or `ghc`. However, just like the
Docker container, a pre-built version of the Shakefile is included as
`1lab-shake`:

```bash
$ 1lab-shake all -j
```

Since `nix-shell` will load the derivation steps as environment
variables, you can use something like this to copy the static assets
into place:

```bash
$ export out=_build/site
$ echo "${installPhase}" | bash
```

## Directly

If you're feeling brave, you can try to replicate one of the build
environments above. You will need:

- A Haskell package manager (either cabal or stack);

- A working LaTeX installation (TeXLive, etc) with the packages
`tikz-cd` (depends on `pgf`), `mathpazo`, `xcolor`, `preview`, and
`standalone` (depends on `varwidth` and `xkeyval`);

- [Poppler] (for `pdftocairo`);
- [`libsass`] (for `sassc`);
- [Node] + required Node modules. Run `npm ci` to install those.

- If you're using Stack, that's all. If using cabal-install, you're
going to need the packages list `support/shake/1lab-shake.cabal`.

[Poppler]: https://poppler.freedesktop.org/
[Node]: https://nodejs.org/en/
[`libsass`]: https://github.com/sass/sassc

If everything is set up properly, the following command should work to
produce the compiled HTML, SVG and CSS files in `_build/html`. You can
then follow either the `support/make-site.sh` script or the
`installPhase` in `default.nix` to work out how to acquire & set up the
rest of the static assets.

```bash
$ stack run -- shake -j all    # (using stack)
$ runghc ./Shakefile.hs all -j # (using cabal-install)
```
