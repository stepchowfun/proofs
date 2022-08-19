# Maintainers

This document describes some instructions for maintainers. Other contributors and users need not be concerned with this material.

### GitHub instructions

When setting up the repository on GitHub, configure the following settings:

- Under `Secrets`:
  - Under `Actions`, add the `DOCKER_PASSWORD` repository secret with an appropriate value.
  - Under `Dependabot`, add the `DOCKER_PASSWORD` repository secret with an appropriate value (e.g., that of the corresponding secret above).
- Under `Branches`, add a branch protection rule for the `main` branch.
  - Enable `Require status checks to pass before merging`.
    - Enable `Require branches to be up to date before merging`.
    - Add the `Validate` status check.
  - Enable `Include administrators`.
- Under `Options`, enable `Automatically delete head branches`.
