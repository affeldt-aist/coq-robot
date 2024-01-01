<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Formal Foundations for Modeling Robot Manipulators

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/affeldt-aist/robot/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/affeldt-aist/robot/actions?query=workflow:"Docker%20CI"




This repository contains an experimental library for the mathematics
of rigid body transformations using the Coq proof-assistant and the
Mathematical Components library.

## Meta

- Author(s):
  - Reynald Affeldt, AIST (initial)
  - Cyril Cohen, Inria (initial)
  - Laurent Théry, Inria
- License: [LGPL-2.1-or-later](LICENSE)
- Compatible Coq versions: Coq 8.14 to Coq 8.18
- Additional dependencies:
  - [MathComp ssreflect](https://math-comp.github.io)
  - [MathComp fingroup](https://math-comp.github.io)
  - [MathComp algebra](https://math-comp.github.io)
  - [MathComp solvable](https://math-comp.github.io)
  - [MathComp field](https://math-comp.github.io)
  - [MathComp analysis](https://github.com/math-comp/analysis)
  - [MathComp real closed](https://github.com/math-comp/real-closed)
- Coq namespace: `robot`
- Related publication(s):
  - [Formal foundations of 3D geometry to model robot manipulators](https://staff.aist.go.jp/reynald.affeldt/documents/robot_cpp_long.pdf) doi:[10.1145/3018610.3018629](https://doi.org/10.1145/3018610.3018629)

## Building and installation instructions

The easiest way to install the latest released version of Formal Foundations for Modeling Robot Manipulators
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-robot
```

To instead build and install manually, do:

``` shell
git clone https://github.com/affeldt-aist/robot.git
cd robot
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Acknowledgments

Contribution by Damien Rouhling (9b7badc25bf6492f6b84611c7f9d32594b345308)

Grant-in-Aid for Scientific Research Number 15H02687

## Disclaimer

This library is still at an experimental stage.  Contents may change
and definitions and theorems may be renamed.  Use at your own risk.

## Documentation

This library can be used to address the forward kinematics problem
of robot manipulators.  It contains theories for angles,
three-dimensional geometry (including three-dimensional rotations,
skew-symmetric matrices, quaternions), rigid body transformations
(isometries, homogeneous representation, Denavit-Hartenberg
convention, screw motions), and an application to the SCARA robot
manipulator.

Each file is documented more precisely in its header.

Some references used in this work:
- [murray] Murray, Li, Shankar Sastry: A Mathematical Introduction to Robotic Manipulation
- [springer] Siciliano, Khatib (Eds.): Springer Handbook of Robotics
- [angeles] Angeles: Fundamentals of Robotic Mechanical Systems, Springer 2014
- [oneill] O'Neill: Elementary Differential Geometry
- [spong] Spong, Hutchinson, Vidyasagar: Robot Modeling and Control
- [sciavicco] Sciavicco, L., Siciliano, B.: Modelling and Control of Robot Manipulators, Springer 2000
- [bottema] Bottema, O., Roth, B.: Theoretical Kinematics, Dover 1990

## Original License

Before [2021-04-29], coq-robot was distributed under the terms of the
`LGPL-3.0` license.
