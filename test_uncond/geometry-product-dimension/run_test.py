#!/usr/bin/env python3
"""Execute only this problem through its README and the installed Yui runtime."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'entry_support'))
from exercise_entry import main
if __name__=='__main__':raise SystemExit(main(Path(__file__).resolve().parent))
