# PinLink README

PinLink is a VSCode extension designed for pinning and linking states in Rocq (formerly known as Coq). It helps users track proof states, link related states, and navigate between them efficiently.

## Features

### Track and Link States

![Link and Diff States](https://github.com/liukatkat/pinlink/blob/main/screenshots/link_diff_state.gif)

> Tip: Check the "Show Diff" button to see the differences compared to the linked states.

### Pin and Refresh States

![Pin and Refresh States](https://github.com/liukatkat/pinlink/blob/main/screenshots/pin_state.gif)

> Tip: Use the "Refresh" button to update all tracked states with the latest proof results.

The files used in the screenshots can be found in the `examples` directory.

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
using VSCode. You may test the extension on the files found in the `examples` directory.

> Tip: It is recommended to start a new debugging instance every time you test on a different file.

---
