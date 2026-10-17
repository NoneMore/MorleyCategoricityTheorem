## Summary

<!-- What changed, and why? -->

## Scope

- [ ] Lean code
- [ ] Blueprint
- [ ] Documentation or repository infrastructure only

## Validation

<!-- List the commands or checks you ran, for example:
- lake build MorleyCategoricityTheorem
- lake exe mk_all --check
- lake exe checkdecls blueprint/lean_decls
-->

## Checklist

- [ ] The pull request is focused and does not include unrelated changes.
- [ ] I ran the relevant validation for the files changed, or explained why I could not.
- [ ] If Lean modules were added, removed, or renamed, `lake exe mk_all --check` passes.
- [ ] If Lean declarations referenced by the blueprint changed, `lake exe checkdecls blueprint/lean_decls` passes.
- [ ] If the blueprint or project homepage changed, the documentation validation workflow passes.
- [ ] I did not introduce unintended `sorry` placeholders.
- [ ] I changed the blueprint only if this pull request intentionally includes blueprint work.
- [ ] I linked relevant issues or blueprint nodes when applicable.
- [ ] The title follows the commit-subject format in `CONTRIBUTING.md`, for example
      `docs: refine AGENTS.md validation guidance`.
