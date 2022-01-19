with builtins;
with import <nixpkgs> {};
let
  agda-fold-equations = haskellPackages.callCabal2nix
    "agda-fold-equations"
    (fetchGit {
      url = "https://git.amelia.how/amelia/agda-fold-equations.git";
      rev = "509bc021200b0de7713a0fdb27c730eaff3be206";
    }) {};

  agda-reference-filter = haskellPackages.callCabal2nix
    "agda-fold-equations"
    (fetchGit {
      url = "https://git.amelia.how/amelia/agda-reference-filter.git";
      rev = "082b5576e799fe8aa28e7d09cf415ac6c9e0596b";
    }) {};

  our-ghc = ghc.withPackages (pkgs: with pkgs; [
    shake directory tagsoup
    text containers uri-encode
    process aeson Agda
  ]);

  our-texlive = texlive.combine {
    inherit (texlive)
      collection-basic
      collection-latex
      xcolor
      preview
      pgf tikz-cd
      mathpazo
      varwidth xkeyval standalone;
  };

  make-font = { type, family, hash, prefix ? "$out" }:
    let
      p = fetchurl {
        url = "https://cubical.1lab.dev/static/${type}/${family}.${type}";
        sha256 = hash;
      };
    in ''
      mkdir -p ${prefix}/static/${type};
      install -Dm 644 ${p} ${prefix}/static/${type}/${family}.${type};
    '';

  fonts = { prefix ? "$out" }: concatStringsSep "\n" (map make-font [
    {
      type = "woff2";
      family = "iosevk-abbie-regular";
      hash = "1zpn3qam0xywvmzz5mjjh23asx9ysnp6ali1agr770qimlxi5zmc";
      inherit prefix;
    }
    {
      type = "ttf";
      family = "iosevk-abbie-regular";
      hash = "0x9nbpm3jf18wlpd7ysbgzl31lwr6qiip5496ma8l72pn812k39g";
      inherit prefix;
    }
  ]);

  shakefile = stdenv.mkDerivation {
    name = "1lab-shake";
    src = filterSource (path: type: match ".*Shakefile.*" path != null) ./.;
    buildInputs = [ our-ghc ];

    buildPhase = ''
    ghc Shakefile.hs
    '';

    installPhase = ''
    mkdir -p $out/bin
    cp Shakefile $out/bin/1lab-shake
    '';
  };
in
  stdenv.mkDerivation rec {
    name = "cubical-1lab";
    src =
      filterSource
        (path: type:
          match ".+\\.agdai$" path == null &&
          match "^_build/.*$" path == null)
        ./.;

    buildInputs = [
      # For driving the compilation:
      shakefile agda

      # For building the text and maths:
      git sassc pandoc nodePackages.katex
      agda-reference-filter agda-fold-equations

      # For building diagrams:
      poppler_utils rubber our-texlive

      # Static fonts:
      gyre-fonts
    ];

    buildPhase = ''
    export LANG=C.UTF-8;
    1lab-shake all -j
    '';

    installPhase = ''
    mkdir -p $out{,/css/,/lib/};

    # Copy our build artifacts
    cp -Lrv _build/html/* $out;

    # Copy KaTeX CSS and fonts
    cp -Lrv --no-preserve=mode ${nodePackages.katex}/lib/node_modules/katex/dist/{katex.min.css,fonts} $out/css/;

    # Copy bits of Iosevka
    ${fonts {}}

    # Copy bits of TeX Gyre
    install -Dm 644 {${gyre-fonts}/share/fonts/truetype/,$out/static/otf/}texgyrepagella-bold.otf;
    install -Dm 644 {${gyre-fonts}/share/fonts/truetype/,$out/static/otf/}texgyrepagella-regular.otf;
    install -Dm 644 {${gyre-fonts}/share/fonts/truetype/,$out/static/otf/}texgyrepagella-italic.otf;
    install -Dm 644 {${gyre-fonts}/share/fonts/truetype/,$out/static/otf/}texgyrepagella-bolditalic.otf;

    # Copy Agda interface files
    for f in src/**/*.agdai; do
      install -Dm 644 $f $out/lib/''${f#$(dirname "$(dirname "$f")")}
    done;
    install -Dm 644 _build/all-pages.agdai $out/lib/all-pages.agdai
    '';

    passthru = {
      deps = [
        shakefile

        # For building the text and maths:
        git sassc pandoc nodePackages.katex
        agda-reference-filter agda-fold-equations
        python

        # For building diagrams:
        poppler_utils rubber
      ];

      texlive = our-texlive;
      fonts = fonts;
    };
  }
