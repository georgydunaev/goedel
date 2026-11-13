#!/usr/bin/env python3
"""Test runner integration for arithmetization suite."""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tests"))

from arithmetization_suite import ArithmetizationPropertySuite

if __name__ == "__main__":
    unittest.main()
