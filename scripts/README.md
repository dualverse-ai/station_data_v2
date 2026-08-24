# Scripts

- `export.py` exports the Station instances listed in `catalog.json` into the viewer data format.
- `validate.py` validates the exported data.
- `serve.py` serves the viewer locally.
- `build_pages.py` builds the GitHub Pages site.
- `browser_qc.mjs` captures the viewer for visual checks.

## Workflow

To import Station data, validate it, and open the viewer locally, run:

```bash
python3 scripts/export.py --station-source-root /path/to/stations
python3 scripts/validate.py
python3 scripts/serve.py
```
