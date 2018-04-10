# Program Verification: Project 2

[![build status](/../badges/master/build.svg)](/../commits/master)

Structure of the repository:

+   `VerifierProject` – the directory that contains the initial files
    of the project.
+   `scala-smtlib` – the directory that contains the library for parsing
    and creating files in the SMTLIB format.
+   `silver` – the directory that contains the definition of the Viper
    language.
+   `docker` – the definition of the Docker image used by the GitLab
    build. It is provided for those who would like to reproduce the
    build environment on their computers. You can safely ignore this
    folder.

Quick start (assuming you have SBT installed):

1.  Run all tests:

    ```
    cd VerifierProject
    sbt
    test
    ```

2.  Run your verifier on a single file:

    ```
    cd VerifierProject
    sbt
    run src/test/resources/MyTests/lecture-pairs.vpr
    ```
