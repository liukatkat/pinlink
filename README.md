# PinLink README

PinLink is a VSCode extension designed for pinning and linking states in Rocq (formerly known as Coq). It helps users track proof states, link related states, and navigate between them efficiently.

## Features

- **Track States**: Pin proof states at specific points in your Coq code.
- **Link States**: Create links between related proof states for better organization.
- **Refresh States**: Recalculate proof states by sending the corresponding code to Coq.
- **Navigate to States**: Quickly jump to the location of a pinned state in your code.
- **Visualize Proof States**: View proof states and their relationships in a sidebar.

### Screenshots

> Tip: Check the "Show Diff" button to see the differences compared to the linked states.

> Tip: Use the "Refresh" button to update all tracked states with the latest proof results.

## Requirements

- **VSCode**: Version 1.70.0 or higher.
- **Coq**: Ensure `coqtop` is installed and available in your system's PATH.
- **Node.js**: Required for building and running the extension.

To install the dependencies, run `npm install`.

## Known Issues

- Doesn't retain pin/ linked states after window is closed
- Doesn't work between different files
- Doesn't handle the case where `coqtop` errors
- State diff is basic text diff
- Navigation to states is buggy

## Release Notes

This extension is unreleased. To try this extension, clone the repo locally and start debugging
using VSCode. You may test the extension on the files found in the `./examples` directory.

> Tip: It is recommended to start a new debugging instance every time you test on a different file.

---
