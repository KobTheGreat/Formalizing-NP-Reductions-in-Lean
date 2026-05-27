# PSet1

This repository contains **Problem Set 1** for the course, written in **Lean 4**.

The problems are located in:

```
pset1/Basic.lean
````

You should only need to edit this file.

---

## Prerequisites

You will need:

- **Lean 4** (installed via `elan`)
- **Lake** (comes with Lean)

If you do not have Lean installed, follow the official instructions:
https://lean-lang.org/lean4/doc/setup.html

---

## Getting Started

Build the project once to download dependencies:

```bash
lake build
```

This may take a few minutes the first time.

If the build succeeds, your setup is working.

---

## Working on the Problem Set

Open the project in **VS Code**:

```bash
code .
```

Make sure you have the **Lean 4 extension** installed.

Open:

```
pset1/Basic.lean
```

Fill in the solutions where indicated.

Lean should show goals and errors directly in the editor.

---

## Checking Your Work

To check that your solutions compile, run:

```bash
lake build
```

Lean must build **without errors** before submission.

---

Another way to check if the solutions compile is through the online lean4 compiler:
https://live.lean-lang.org/<br>

Simply copy and paste the code in `pset1/Basic.lean` into the editor to check for errors.

---

## Common Issues

* If `lake build` fails the first time, try running it again.
* Make sure you opened the **project root** (`pset1/`), not just the `.lean` file.
* If Lean shows `unknown package`, ensure you ran `lake build` successfully.

---

## Submission

Submit your completed `pset1/Basic.lean` file according to the course instructions.

Do **not** modify other files unless instructed.

---

## Notes

* Do not rename files or folders.
* Do not change the project structure.
* If something seems broken, ask on the course forum.