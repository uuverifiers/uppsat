# UppSat
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


## Running the tests

When running sbt assembly a set of test-cases will be run automatically.

## Built With

* [SBT](http://www.scala-sbt.org/) - Simple Build Tool
* [Scala](https://www.scala-lang.org/) - Scala 

## License


[![Build Status](https://travis-ci.org/uuverifiers/uppsat.svg?branch=master)](https://travis-ci.org/uuverifiers/uppsat)
