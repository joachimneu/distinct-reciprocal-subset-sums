# Git Operations

Unless the user has explicitly instructed you to do so, do not touch the staging area in any way.
This includes adding to the index (e.g., `git add`), removing from the index (e.g., `git reset`, `git restore --staged`, `git rm --cached`), or otherwise modifying what is staged.
Likewise, do not commit (`git commit`) changes unless explicitly instructed.
This applies even when changes appear complete, when the working tree is dirty, or when staging or committing would seem like a natural next step.
Leave the working tree and the index as-is and let the user decide when and what to stage or commit.
