Deliver a static replacement for the supplied reference CLI. Its input and output are
byte streams. LF separates lines. Remove spaces (0x20) and tabs (0x09) at each line
end, including the final unterminated line. Preserve all other bytes, empty lines
and the presence or absence of a final LF. With exactly ["--check"] and any change,
exit 2 with both streams empty. Otherwise write the cleaned stream and exit 0 with
empty stderr. This includes clean input in check mode.

Use a single tree named Trim with a CLI entry. Observe the real reference before
driving the tree. Use read_context for the SessionEnv and World APIs, write_draft
for source, run_lean_script for the observation, and check_spec for the behavioral
contract. Give the node byte-level operations and universal laws that characterize
line trimming and the process observations. Leave the choice of algorithm to the
node. Keep the tree small enough to implement in one leaf if appropriate. Use Lean
syntax throughout. A leaf should read its world API with read_context, save its
implementation with write_draft, and pass check_lean and check_plan before submitting.

After drive-tree returns ok, use check_entry and submit build-exe. Write a typed
differential probe using SessionEnv.replay for dirty and clean inputs with and
without --check. Propagate any mismatched result; use run_lean_script to check the
probe and submit run-script to record the comparison. Finish with a short summary
of the observed behavior and test cases. Each proposal fork submits one action.
