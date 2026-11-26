# EX-K3-C5-CERT-1.0: Constructive Capacity, Sum-of-Squares, and Shadow-Reduction Certificates for Triangles Without Pentagons

**Author:** Lluis Eriksson (`lluis@airr.science`)  
**Schema:** `EX-K3-C5-CERT-1.0`  
**Target Preprint:** Qing Cui, Ervin Győri, Chenke Zhang, and Xiutao Zhu, *"The maximum number of triangles in a graph without pentagons"* (`arXiv:2611.33685v1`, November 25, 2026).

## Overview
This repository provides an independently reproducible, zero-floating-point Python verification engine (`src/ex_k3_c5_verifier.py`), a constructive Lean 4.35.0 kernel (`lean/TrianglesNoPentagonsCert.lean`, 18 constructive theorems, 0 `sorry`, 0 custom axioms, 0 `Classical.choice`, 0 warnings), 16 canonical JSON certificates (`certificates/C01..C16`), unit and adversarial forgery tests (`tests/test_verifier.py`), 3 publication figures, and a 4-page LaTeX/PDF companion paper (`paper/main.pdf`).

## Quick Reproduction
```bash
cd lean && lake build && cd ..
python -m src.ex_k3_c5_verifier certificates/
pytest -q
python scripts/build_manifest.py --check
```

## Licenses & Disclosure
- Manuscript & figures: `CC-BY-4.0`
- Code, Lean proofs & certificates: `MIT`
- Produced with Google Antigravity assistance; independently compiled, verified, and reviewed by Lluis Eriksson.
