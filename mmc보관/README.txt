mm.c version archive (score-tiered)
location: C:\Users\Administrator\Desktop\github\malloc\completely_done\mmc보관

Purpose
- Keep multiple allocator implementations by complexity/score tier.
- Start from lower score (60+) and move up to higher score.

Versions
1) mm_v60plus_implicit_scan_realloc_copy.c
   - Structure:
     - explicit free list metadata is still maintained
     - find_fit uses implicit whole-heap scan (slow path)
     - realloc uses simple malloc-copy-free only
   - Measured score (mdriver -g in Docker): perfidx 66
   - Use case: baseline that passes but is intentionally slower.

2) mm_v70plus_explicit_basic_realloc_copy.c
   - Structure:
     - explicit free list + first-fit
     - immediate coalescing + split
     - realloc uses simple malloc-copy-free only
   - Measured score (mdriver -g in Docker): perfidx 70
   - Use case: mid-tier implementation, simpler realloc logic.

3) mm_v80plus_explicit_realloc_inplace.c
   - Structure:
     - explicit free list + first-fit
     - immediate coalescing + split
     - realloc has in-place shrink/grow optimization before fallback copy
   - Measured score (mdriver -g in Docker): perfidx 83
   - Use case: high-tier implementation among current archived versions.

How to use a version as active mm.c
1. Backup current mm.c
2. Copy one version file to completely_done/mm.c
3. Build/test

Example (PowerShell):
Copy-Item "C:\Users\Administrator\Desktop\github\malloc\completely_done\mmc보관\mm_v70plus_explicit_basic_realloc_copy.c" `
          "C:\Users\Administrator\Desktop\github\malloc\completely_done\mm.c" -Force

Score test command used
docker run --rm -v "C:/Users/Administrator/Desktop/github/malloc:/workspace" `
  -w /workspace/completely_done codex-malloc-dev:latest `
  bash -lc "gcc -I/workspace/completely_done -Wall -O2 -g -o /tmp/mdriver mdriver.c <VERSION_FILE> memlib.c fsecs.c fcyc.c clock.c ftimer.c && /tmp/mdriver -g"

Notes
- These scores are measured in this environment; scores can vary slightly by machine/toolchain.
- mdriver warnings shown during compile are from mdriver.c, not from these mm.c versions.

