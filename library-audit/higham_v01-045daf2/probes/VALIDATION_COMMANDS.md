# Harness validation commands

Run from the isolated `_worktree`:

```sh
/usr/bin/time -p -o ../probes/validation_output/KnownVisible_check.time \
  lake env lean -R ../probes/validation \
  -o ../probes/validation_output/KnownVisible_check.olean \
  -i ../probes/validation_output/KnownVisible_check.ilean \
  ../probes/validation/KnownVisible_check.lean

/usr/bin/time -p -o ../probes/validation_output/KnownVisibleBadClient_client.time \
  lake env lean -R ../probes/validation \
  -o ../probes/validation_output/KnownVisibleBadClient_client.olean \
  -i ../probes/validation_output/KnownVisibleBadClient_client.ilean \
  ../probes/validation/KnownVisibleBadClient_client.lean
```

The first command exited 0. The second deliberately ill-typed client exited 1
after successfully printing the `#check` type, validating the separation
between visibility and client-theorem acceptance.
