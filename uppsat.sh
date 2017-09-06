#!/bin/bash
 env JAVA_OPTS="-Xprof" scala target/scala-2.11/uppsat-assembly-0.01.jar $*
