{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/rocq-overlays`
  ## and `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "CertiCoq";

  no-rocq-yet = true;

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  default-bundle = "9.1";
  ## When generating GitHub Action CI, one workflow file
  ## will be created per bundle
  bundles."9.1" = { coqPackages = {
      coq.override.version = "9.1";
      compcert.job = false;
      compcert.override.version = "3.17";
      wasmcert.job = false;
      wasmcert.override.version = "v2.2.0";
      metarocq.job = false;
      metarocq.override.version = "1.4.1-9.1";
    }; rocqPackages = {
      rocq-core.override.version = "9.1";
    };
  };

  bundles."9.1".push-branches = ["master"];

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community = { };
  cachix.metarocq = {};
}
