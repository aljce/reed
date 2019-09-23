# A fully reproducible python build environment via nix
# run `nix-shell` to enter the build enviroment
with rec {
  fetch-github =
    { owner  # The owner of the repo
    , repo   # The repo to fetch
    , rev    # The git commit hash you want
    , sha256 # The SHA256 hash of the unpacked archive (for reproducibility)
    }: builtins.fetchTarball {
      url = "https://github.com/${owner}/${repo}/archive/${rev}.tar.gz";
      inherit sha256;
    };
  nixpkgs-src = fetch-github {
    owner  = "NixOS";
    repo   = "nixpkgs";
    rev    = "56d94c8c69f8cac518027d191e2f8de678b56088"; # stable 19.03
    sha256 = "1c812ssgmnmh97sarmp8jcykk0g57m8rsbfjg9ql9996ig6crsmi";
  };
  nixpkgs = import nixpkgs-src { overlays = []; };
};
with rec {
  python-packages = py-pkgs: with py-pkgs; [
    tkinter
  ];
  python3 = nixpkgs.python3.withPackages python-packages;
};
nixpkgs.stdenv.mkDerivation {
  name = "cs389-hw1";
  buildInputs = [ python3 ];
}
