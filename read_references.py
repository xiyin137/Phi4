#!/usr/bin/env python3
"""
Read PDF files from the references folder (READ-ONLY).

This script extracts text from PDF files in the references/ directory.
Useful for searching mathematical content from reference materials.

NOTE: This script is strictly read-only. It never writes or modifies any files.
All output goes to stdout only.

Usage:
    python read_references.py                    # List all PDFs
    python read_references.py <filename>         # Extract text from specific PDF
    python read_references.py --search <term>    # Search for term in all PDFs
    python read_references.py <filename> --page <n>  # Extract specific page
"""

import os
import sys
from pathlib import Path

# Try to import PDF libraries
try:
    import fitz  # PyMuPDF
    HAS_PYMUPDF = True
except ImportError:
    HAS_PYMUPDF = False

try:
    from pypdf import PdfReader
    HAS_PYPDF = True
except ImportError:
    try:
        from PyPDF2 import PdfReader
        HAS_PYPDF = True
    except ImportError:
        HAS_PYPDF = False

REFERENCES_DIR = Path(__file__).parent / "references"


def list_pdfs():
    """List all PDF files in the references directory."""
    if not REFERENCES_DIR.exists():
        print(f"References directory not found: {REFERENCES_DIR}")
        return []

    pdfs = list(REFERENCES_DIR.glob("*.pdf"))
    if not pdfs:
        print("No PDF files found in references/")
        return []

    print(f"PDF files in {REFERENCES_DIR}:")
    for i, pdf in enumerate(pdfs, 1):
        size_mb = pdf.stat().st_size / (1024 * 1024)
        print(f"  {i}. {pdf.name} ({size_mb:.1f} MB)")
    return pdfs


def extract_text_pymupdf(pdf_path: Path, page_num: int = None) -> str:
    """Extract text using PyMuPDF (fitz)."""
    doc = fitz.open(pdf_path)
    text_parts = []

    if page_num is not None:
        if 0 <= page_num < len(doc):
            page = doc[page_num]
            text_parts.append(f"=== Page {page_num + 1} ===\n")
            text_parts.append(page.get_text())
        else:
            print(f"Page {page_num + 1} out of range (document has {len(doc)} pages)")
    else:
        for i, page in enumerate(doc):
            text_parts.append(f"\n=== Page {i + 1} ===\n")
            text_parts.append(page.get_text())

    doc.close()
    return "".join(text_parts)


def extract_text_pypdf(pdf_path: Path, page_num: int = None) -> str:
    """Extract text using pypdf/PyPDF2."""
    reader = PdfReader(pdf_path)
    text_parts = []

    if page_num is not None:
        if 0 <= page_num < len(reader.pages):
            page = reader.pages[page_num]
            text_parts.append(f"=== Page {page_num + 1} ===\n")
            text_parts.append(page.extract_text() or "")
        else:
            print(f"Page {page_num + 1} out of range (document has {len(reader.pages)} pages)")
    else:
        for i, page in enumerate(reader.pages):
            text_parts.append(f"\n=== Page {i + 1} ===\n")
            text_parts.append(page.extract_text() or "")

    return "".join(text_parts)


def extract_text(pdf_path: Path, page_num: int = None) -> str:
    """Extract text from a PDF file."""
    if HAS_PYMUPDF:
        return extract_text_pymupdf(pdf_path, page_num)
    elif HAS_PYPDF:
        return extract_text_pypdf(pdf_path, page_num)
    else:
        print("Error: No PDF library available.")
        print("Install one of:")
        print("  pip install pymupdf")
        print("  pip install pypdf")
        sys.exit(1)


def search_pdfs(search_term: str):
    """Search for a term in all PDFs."""
    pdfs = list(REFERENCES_DIR.glob("*.pdf"))
    if not pdfs:
        print("No PDF files found")
        return

    print(f"Searching for '{search_term}' in {len(pdfs)} PDF(s)...\n")

    for pdf_path in pdfs:
        print(f"Searching {pdf_path.name}...")
        text = extract_text(pdf_path)

        # Find all occurrences
        search_lower = search_term.lower()
        text_lower = text.lower()

        if search_lower in text_lower:
            # Find context around matches
            lines = text.split('\n')
            for i, line in enumerate(lines):
                if search_lower in line.lower():
                    # Print surrounding context
                    start = max(0, i - 1)
                    end = min(len(lines), i + 2)
                    print(f"\n  Found in {pdf_path.name}:")
                    for j in range(start, end):
                        marker = ">>>" if j == i else "   "
                        print(f"  {marker} {lines[j][:100]}")
        else:
            print(f"  No matches in {pdf_path.name}")


def main():
    if len(sys.argv) == 1:
        # No arguments: list PDFs
        list_pdfs()
        print("\nUsage:")
        print("  python read_references.py <filename>         # Extract text")
        print("  python read_references.py <filename> --page <n>  # Extract page n")
        print("  python read_references.py --search <term>    # Search all PDFs")
        return

    if sys.argv[1] == "--search":
        if len(sys.argv) < 3:
            print("Usage: python read_references.py --search <term>")
            return
        search_term = " ".join(sys.argv[2:])
        search_pdfs(search_term)
        return

    # Extract text from specific PDF
    pdf_name = sys.argv[1]
    pdf_path = REFERENCES_DIR / pdf_name

    if not pdf_path.exists():
        # Try adding .pdf extension
        pdf_path = REFERENCES_DIR / f"{pdf_name}.pdf"
        if not pdf_path.exists():
            print(f"PDF not found: {pdf_name}")
            list_pdfs()
            return

    # Check for page number
    page_num = None
    if "--page" in sys.argv:
        page_idx = sys.argv.index("--page")
        if page_idx + 1 < len(sys.argv):
            try:
                page_num = int(sys.argv[page_idx + 1]) - 1  # Convert to 0-indexed
            except ValueError:
                print("Invalid page number")
                return

    print(f"Extracting text from: {pdf_path.name}")
    if HAS_PYMUPDF:
        print("Using: PyMuPDF")
    elif HAS_PYPDF:
        print("Using: pypdf")
    print("-" * 50)

    text = extract_text(pdf_path, page_num)
    print(text)


if __name__ == "__main__":
    main()
