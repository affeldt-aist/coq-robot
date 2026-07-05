{ lib, mkRocqDerivation, rocq-core, stdlib
, hierarchy-builder, mathcomp-fingroup, mathcomp-algebra
, mathcomp-solvable, mathcomp-field, mathcomp-analysis
, mathcomp-real-closed
}:

mkRocqDerivation {
  pname = "robot-rocq";
  owner = "affeldt-aist";
  version = "dev";
  src = ../../..;

  propagatedBuildInputs = [
    hierarchy-builder
    mathcomp-fingroup
    mathcomp-algebra
    mathcomp-solvable
    mathcomp-field
    mathcomp-analysis
    mathcomp-real-closed

  ];

  meta = {
    description = "Formal Foundations for Modeling Robot Manipulators";
    license = lib.licenses.lgpl21Plus;
  };
}