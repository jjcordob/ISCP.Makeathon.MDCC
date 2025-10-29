# 🔍 Vision-First Document Processing

## Overview

DVM now includes an **optional AI Vision Pre-filtering** feature that dramatically improves accuracy by processing documents as images first, filtering out irrelevant content before text extraction and code generation.

## How It Works

### Traditional Text-Based Approach
```
PDF/DOCX → Extract All Text → Keyword Search → Generate Code
         (includes TOC, references, headers, etc.)
```

### Vision-First Approach ✨
```
PDF/DOCX → Convert to Images → AI Vision Analysis → Filter Pages → 
           Extract Only Relevant Text → Generate Code
```

## The Vision Pipeline

### 1. **Page-to-Image Conversion**
- Converts each document page to a high-resolution image (200 DPI)
- Preserves visual layout, formatting, and structure
- Supports: PDF, DOCX, TXT, MD

### 2. **AI Vision Analysis** 👁️
For each page image, the AI analyzes:
- **Assertions Mode**: Looks for properties, requirements, protocols, must/shall statements
- **Covergroups Mode**: Looks for test scenarios, coverage specs, corner cases, states

Scoring (0-10):
- **8-10**: Direct specification content → KEEP
- **5-7**: Useful design details → KEEP
- **2-4**: Tangential content → DISCARD
- **0-1**: Completely irrelevant (TOC, title pages) → DISCARD

### 3. **Intelligent Filtering**
- Discards pages like:
  - Table of contents
  - Title pages
  - Bibliography/References
  - Generic background information
  - Unrelated specifications

- Keeps pages with:
  - Specific requirements
  - Protocol definitions
  - Test scenarios
  - Coverage specifications
  - Design constraints

### 4. **Focused Processing**
- Extracts text ONLY from relevant pages
- Sends filtered content to AI agents
- Results in cleaner, more accurate code generation

## Benefits

### 🎯 Higher Accuracy
- **Reduces noise**: No more TOC or reference sections confusing the AI
- **Better focus**: AI agents work with only relevant content
- **Fewer hallucinations**: Less irrelevant information = fewer incorrect assumptions

### ⚡ Efficiency
- **Faster processing**: Analyzing 5 relevant pages instead of 50 total pages
- **Lower costs**: Fewer tokens sent to AI models
- **Better results**: Concentrated, high-quality input → better output

### 📊 Transparency
- See exactly which pages were kept/discarded
- Understand why pages were filtered
- View AI reasoning for each page

## Usage

### In the GUI
1. Upload your document (PDF/DOCX/TXT/MD)
2. ✅ Check **"🔍 Use AI Vision Pre-filtering (Recommended)"**
3. Select output mode (Assertions or Covergroups)
4. Click **Process**

### What You'll See
```
👁️ Step 1/7: Converting document pages to images...
✓ Analyzed 15 pages with AI vision
  📊 Kept: 5 pages | Discarded: 10 pages (66.7% filtered)
  Top relevant pages:
    Page 3: Score 9/10 - assertion, protocol, must
    Page 7: Score 8/10 - coverage, test case, scenario
    Page 12: Score 8/10 - requirement, shall, verify
```

## Examples

### Example: Requirements Document (50 pages)

**Without Vision Filtering:**
- Processes all 50 pages
- Includes: TOC (2 pages), intro (5 pages), references (3 pages)
- AI sees 50,000+ words
- Results: Mixed quality, some incorrect assumptions

**With Vision Filtering:**
- Analyzes 50 pages visually
- Keeps: 12 relevant pages with actual requirements
- Discards: 38 pages (TOC, intro, background, references)
- AI sees 12,000 relevant words
- Results: Highly accurate, focused assertions

### Example Filter Log
```
Page 1: Score 1/10 - Title page, no technical content → DISCARD
Page 2: Score 2/10 - Table of contents → DISCARD  
Page 5: Score 4/10 - General introduction → DISCARD
Page 8: Score 9/10 - Protocol requirements with must/shall → KEEP
Page 12: Score 8/10 - Coverage scenarios and test cases → KEEP
Page 45: Score 2/10 - Bibliography → DISCARD
```

## Requirements

### Required
- `PyMuPDF>=1.23.0` (for PDF → image conversion)
- `Pillow>=10.0.0` (image processing)

### Installation
```bash
pip install PyMuPDF Pillow
```

### Alternative (if PyMuPDF not available)
```bash
pip install pdf2image
# Requires poppler: https://github.com/oschwartz10612/poppler-windows/releases/
```

## Configuration

The vision analyzer uses strict scoring criteria:

```python
# Configure in vision_document_processor.py
SCORE_THRESHOLD = 5.0  # Minimum score to keep page
TOP_N_PAGES = None     # None = keep all above threshold
```

## Limitations

### When NOT to Use Vision Filtering
- ❌ **Short documents** (< 5 pages) - overhead not worth it
- ❌ **Plain text files** - vision doesn't add value
- ❌ **Already filtered documents** - if document only contains relevant content
- ❌ **Scanned documents with poor quality** - OCR accuracy issues

### When TO Use Vision Filtering ✅
- ✅ **Large specification documents** (20+ pages)
- ✅ **Mixed-content PDFs** (TOC, appendices, references)
- ✅ **Standards documents** (lots of boilerplate)
- ✅ **Multi-chapter documents** (only some chapters relevant)

## Performance

### Typical Performance
- **Page conversion**: ~0.5s per page
- **Vision analysis**: ~2s per page (AI call)
- **Text extraction**: ~0.1s per page

### Example: 30-page document
- Without vision: ~20s to process all pages
- With vision: ~75s for filtering + ~5s for 5 relevant pages = ~80s total
- **Trade-off**: Slightly slower, but MUCH more accurate

## Tips for Best Results

1. **Use for large documents**: Vision filtering shines with 20+ page docs
2. **Check the filter log**: Review which pages were kept/discarded
3. **Adjust if needed**: If too many pages discarded, disable filtering
4. **Combine with standard**: Try both and compare results

## Troubleshooting

### "PyMuPDF not installed"
```bash
pip install PyMuPDF
```

### "No relevant pages found"
- Document may not contain assertion/coverage content
- Try unchecking vision filtering
- Check if you selected correct mode (assertions vs covergroups)

### "Vision analysis taking too long"
- Normal for large documents (2s per page)
- Consider processing smaller sections
- Use standard text analysis for quick tests

## Future Enhancements

- [ ] OCR support for scanned documents
- [ ] Batch processing multiple documents
- [ ] Custom filtering criteria
- [ ] Multi-page analysis (context across pages)
- [ ] Visual section extraction

---

**Recommendation**: Enable vision filtering for specification documents larger than 10 pages. The accuracy improvement is worth the extra processing time!
