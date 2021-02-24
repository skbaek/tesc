# Test Environment

In order to replicate the test results in the paper, it is recommended that 
you use the same versions for the following programs and libraries.

- TPTP problem library : v7.4.0
- Vampire : Version [4.5.1](https://github.com/vprover/vampire/releases/tag/4.5.1), built with `make vampire_rel` 
- E : 2.5 Avongrove, commit [a8acce0b281f27282ba15f0a8541e54662223340](https://github.com/eprover/eprover/commit/a8acce0b281f27282ba15f0a8541e54662223340)
- DRAT-trim : commit [d13f761fbdacd052429f14421f95a7e8cd75deb1](https://github.com/marijnheule/drat-trim/commit/d13f761fbdacd052429f14421f95a7e8cd75deb1)
- CaDiCaL : commit [c622a490ec3d9a1a1e998b08120c9b8d0b67a123](https://github.com/arminbiere/cadical/commit/c622a490ec3d9a1a1e998b08120c9b8d0b67a123)

Language compiler versions were not as strictly controlled and 
changed from time to time. Since no compiler-related issues were 
encountered, it is unlikely to be critical, but one of the versions 
used for each compiler is listed for reference. 

- swipl : version 8.2.1 for x86_64-linux
- rustc : 1.47.0 (18bf6b4f0 2020-10-07)


# Test Results

For a complete CSV of test results, see [results.csv](https://github.com/skbaek/tesc/blob/cade/results.csv).

Most of the CSV column names are self-explanatory, except for the following:
- first-order : Is the problem in the CNF or FOF language?
- unsatisfiable : Does the problem have "theorem" or "unsatisfiable" status?
- well-formed : Does the problem conform to the official TPTP syntax? In particular, are its 'sq_char's free of the character '%'? 
- unique names : Do its formulas all have unique names?

Note that some cells are marked with `N/A` because either 
(1) the problem was not eligible for the test, or 
(2) some necessary earlier step of the test failed for that problem.