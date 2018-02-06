# UppSAT
An approximating SMT solver

## Getting Started

Clone the repository and use SBT to assemble a stand-alone jar. If custom approximations are to be added, they should be implemented as an ApproximationCore object and added to the command-line options.


### Prerequisites

The project is build using SBT and requires Scala 2.11.8 or newer.

### Installing

git clone ...

cd uuverifiers/uppsat/

sbt assembly

cp target/scala-2.11/uppsat-assembly-0.01.jar uppsat.jar

scala uppsat.jar -app=ijcar -backend=z3 -validator=z3 examples/e2a_1.c.smt2


## Installing back-ends

UppSAT currently supports Z3 and MathSAT as back-ends. To use them, make sure that the programs "z3" and "mathsat" are available on the path (e.g., you can add them to the $PATH environmental variable). The current version of UppSAT has been tested with MathSAT5 5.5.1 and Z3 4.5.0.

## Running the tests

When running sbt assembly a set of test-cases will be run automatically.

## Built With

* [SBT](http://www.scala-sbt.org/) - Simple Build Tool
* [Scala](https://www.scala-lang.org/) - Scala 

## License

[![Build Status](https://travis-ci.org/uuverifiers/uppsat.svg?branch=master)](https://travis-ci.org/uuverifiers/uppsat)
