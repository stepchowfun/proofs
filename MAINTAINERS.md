# Maintainers

This document describes some instructions for maintainers. Other contributors and users need not be concerned with this material.

### GitHub instructions

When setting up the repository on GitHub, configure the following settings:

- Under `Secrets`, add the following repository secrets with appropriate values:
  - `CRATES_IO_TOKEN`
  - `DOCKER_PASSWORD`
- Under `Branches`, add a branch protection rule for the `main` branch.
  - Enable `Require status checks to pass before merging`.
    - Enable `Require branches to be up to date before merging`.
    - Add the `ci` status check.
  - Enable `Include administrators`.
- Under `Options`, enable `Automatically delete head branches`.
