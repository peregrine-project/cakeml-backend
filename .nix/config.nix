{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "CakeMLExtraction";

  no-rocq-yet = true;

  default-bundle = "9.1";

  bundles."9.1" = {
    coqPackages = {
      coq.override.version = "9.1";
      metarocq-utils.override.version = "1.5.1-9.1";
      metarocq-erasure-plugin.override.version = "1.5.1-9.1";
      ceres-bs.override.version = "1.0.0";
    }; rocqPackages = {
      rocq-core.override.version = "9.1";
    };
    push-branches = [ "main" "rocq-9.1" ];
  };



  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  cachix.metarocq = {};
  cachix.peregrine.authToken = "CACHIX_AUTH_TOKEN";
}
