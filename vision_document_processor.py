"""
Vision-First Document Processor for DVM
Uses AI vision to pre-filter document pages for relevant content
before text extraction and code generation
"""

import os
import io
import base64
from pathlib import Path
from typing import Dict, List, Optional, Tuple
import PyPDF2
from PIL import Image
from docx import Document as DocxDocument
from docx.shared import Inches
import tempfile
from config import Config


class DocumentToImageConverter:
    """Converts document pages to images for vision analysis"""
    
    @staticmethod
    def pdf_to_images(pdf_path: str) -> List[Dict[str, any]]:
        """
        Convert PDF pages to images
        
        Args:
            pdf_path: Path to PDF file
            
        Returns:
            List of dicts with page images and metadata
        """
        try:
            import fitz  # PyMuPDF for better rendering
            
            pages = []
            doc = fitz.open(pdf_path)
            
            for page_num in range(len(doc)):
                page = doc[page_num]
                
                # Render page to image at 200 DPI for good quality
                pix = page.get_pixmap(matrix=fitz.Matrix(200/72, 200/72))
                
                # Convert to PIL Image
                img = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)
                
                # Convert to base64
                buffer = io.BytesIO()
                img.save(buffer, format='PNG')
                img_base64 = base64.b64encode(buffer.getvalue()).decode('utf-8')
                
                pages.append({
                    'page_number': page_num + 1,
                    'image': img,
                    'base64': img_base64,
                    'width': pix.width,
                    'height': pix.height
                })
            
            doc.close()
            return pages
            
        except ImportError:
            # Fallback: Try pdf2image
            try:
                from pdf2image import convert_from_path
                
                images = convert_from_path(pdf_path, dpi=200)
                pages = []
                
                for i, img in enumerate(images):
                    buffer = io.BytesIO()
                    img.save(buffer, format='PNG')
                    img_base64 = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    
                    pages.append({
                        'page_number': i + 1,
                        'image': img,
                        'base64': img_base64,
                        'width': img.width,
                        'height': img.height
                    })
                
                return pages
                
            except ImportError:
                raise Exception("Neither PyMuPDF nor pdf2image available. Install: pip install PyMuPDF OR pip install pdf2image")
    
    @staticmethod
    def docx_to_images(docx_path: str) -> List[Dict[str, any]]:
        """
        Convert DOCX to images by rendering pages
        
        Args:
            docx_path: Path to DOCX file
            
        Returns:
            List of dicts with page images and metadata
        """
        try:
            from docx2pdf import convert
            import platform
            
            # Convert DOCX to PDF first (requires Word on Windows, LibreOffice on Linux)
            with tempfile.NamedTemporaryFile(suffix='.pdf', delete=False) as tmp_pdf:
                tmp_pdf_path = tmp_pdf.name
            
            convert(docx_path, tmp_pdf_path)
            
            # Now convert PDF to images
            pages = DocumentToImageConverter.pdf_to_images(tmp_pdf_path)
            
            # Clean up temp PDF
            os.unlink(tmp_pdf_path)
            
            return pages
            
        except ImportError:
            # Fallback: Extract images from DOCX (won't capture text as images)
            raise Exception("docx2pdf not available. For full page rendering, install: pip install docx2pdf")
    
    @staticmethod
    def text_to_image(text: str, page_number: int = 1) -> Dict[str, any]:
        """
        Convert plain text to image for vision analysis
        
        Args:
            text: Text content
            page_number: Page number
            
        Returns:
            Dict with image data
        """
        from PIL import ImageDraw, ImageFont
        
        # Create image (A4 proportions at 200 DPI: 1654x2339)
        img = Image.new('RGB', (1654, 2339), color='white')
        draw = ImageDraw.Draw(img)
        
        # Try to use a monospace font
        try:
            font = ImageFont.truetype("consola.ttf", 20)
        except:
            font = ImageFont.load_default()
        
        # Draw text with word wrapping
        y = 50
        x = 50
        line_height = 30
        max_width = 1554  # Leave margins
        
        for line in text.split('\n'):
            if y > 2239:  # Page overflow
                break
            
            # Simple word wrap
            words = line.split()
            current_line = ""
            
            for word in words:
                test_line = current_line + word + " "
                bbox = draw.textbbox((0, 0), test_line, font=font)
                if bbox[2] - bbox[0] > max_width:
                    if current_line:
                        draw.text((x, y), current_line.strip(), fill='black', font=font)
                        y += line_height
                        current_line = word + " "
                else:
                    current_line = test_line
            
            if current_line:
                draw.text((x, y), current_line.strip(), fill='black', font=font)
                y += line_height
        
        # Convert to base64
        buffer = io.BytesIO()
        img.save(buffer, format='PNG')
        img_base64 = base64.b64encode(buffer.getvalue()).decode('utf-8')
        
        return {
            'page_number': page_number,
            'image': img,
            'base64': img_base64,
            'width': img.width,
            'height': img.height
        }


class VisionPageAnalyzer:
    """Uses AI vision to analyze document pages for relevant content"""
    
    def __init__(self):
        """Initialize vision analyzer with AI agent"""
        from agent import DVMAgent
        self.agent = DVMAgent()
    
    def analyze_page_for_relevance(self, page_data: Dict[str, any], artifact_type: str) -> Dict[str, any]:
        """
        Analyze a page image to determine relevance for assertions or covergroups
        
        Args:
            page_data: Page image data with base64
            artifact_type: 'assertions' or 'covergroups'
            
        Returns:
            Analysis result with relevance score and hints
        """
        artifact_hints = {
            'assertions': """assertions, properties, SVA, formal verification, protocol rules, 
                           requirements, constraints, invariants, safety properties, 
                           must/shall statements, checkers, assume/assert/cover""",
            'covergroups': """coverage, covergroups, coverpoints, functional coverage, 
                            test scenarios, test cases, corner cases, edge cases, 
                            state transitions, bins, cross coverage, coverage metrics"""
        }
        
        hints = artifact_hints.get(artifact_type, "verification requirements")
        
        prompt = f"""Analyze this document page to determine if it contains information relevant for generating {artifact_type.upper()}.

TASK: Scan this page for {artifact_type}-related content.

LOOK FOR these indicators:
{hints}

STRICT SCORING:
- Score 0-10 (0 = completely irrelevant, 10 = highly relevant)
- Be CONSERVATIVE - only high scores for pages with clear {artifact_type} content
- Score 8-10: Direct {artifact_type} specifications or requirements
- Score 5-7: Design details that could inform {artifact_type}
- Score 2-4: Tangential content (general descriptions, background)
- Score 0-1: Completely irrelevant (title pages, TOC, references, etc.)

PROVIDE:
1. SCORE: X/10
2. REASONING: Brief explanation (1-2 sentences)
3. KEY_HINTS: Specific phrases/keywords found that indicate relevance
4. RECOMMENDATION: KEEP or DISCARD

Be strict - we want to filter OUT pages that don't directly contribute to {artifact_type} generation."""

        try:
            # Prepare image data for agent
            image_data = {
                'base64': page_data['base64'],
                'media_type': 'image/png'
            }
            
            # Get vision analysis from agent
            response = self.agent.get_response(prompt, image_data=image_data)
            
            # Parse response to extract score and recommendation
            score = self._extract_score(response)
            recommendation = self._extract_recommendation(response)
            key_hints = self._extract_hints(response)
            
            return {
                'page_number': page_data['page_number'],
                'score': score,
                'recommendation': recommendation,
                'reasoning': response,
                'key_hints': key_hints,
                'is_relevant': recommendation == 'KEEP' and score >= 5
            }
            
        except Exception as e:
            # On error, be conservative - mark as potentially relevant
            return {
                'page_number': page_data['page_number'],
                'score': 5.0,
                'recommendation': 'KEEP',
                'reasoning': f"Error in analysis: {str(e)}",
                'key_hints': [],
                'is_relevant': True
            }
    
    def _extract_score(self, response: str) -> float:
        """Extract score from analysis response"""
        import re
        
        # Look for "SCORE: X/10" or "Score: X"
        score_match = re.search(r'SCORE:?\s*(\d+(?:\.\d+)?)\s*/?\s*10', response, re.IGNORECASE)
        if score_match:
            return float(score_match.group(1))
        
        # Look for standalone number
        score_match = re.search(r'(?:score|rating).*?(\d+(?:\.\d+)?)', response, re.IGNORECASE)
        if score_match:
            return float(score_match.group(1))
        
        return 5.0  # Default middle score if can't parse
    
    def _extract_recommendation(self, response: str) -> str:
        """Extract KEEP/DISCARD recommendation"""
        response_upper = response.upper()
        
        if 'RECOMMENDATION:' in response_upper:
            if 'KEEP' in response_upper.split('RECOMMENDATION:')[1][:50]:
                return 'KEEP'
            elif 'DISCARD' in response_upper.split('RECOMMENDATION:')[1][:50]:
                return 'DISCARD'
        
        # Fallback: look for keywords
        if 'DISCARD' in response_upper or 'NOT RELEVANT' in response_upper:
            return 'DISCARD'
        
        return 'KEEP'
    
    def _extract_hints(self, response: str) -> List[str]:
        """Extract key hints/keywords from response"""
        import re
        
        # Look for KEY_HINTS section
        hints_match = re.search(r'KEY[_\s]HINTS:?\s*(.+?)(?:\n\n|\nRECOMMENDATION|$)', response, re.IGNORECASE | re.DOTALL)
        
        if hints_match:
            hints_text = hints_match.group(1)
            # Split by commas, semicolons, or newlines
            hints = re.split(r'[,;\n]', hints_text)
            return [h.strip() for h in hints if h.strip() and len(h.strip()) > 2][:10]
        
        return []
    
    def batch_analyze_pages(self, pages: List[Dict[str, any]], artifact_type: str) -> List[Dict[str, any]]:
        """
        Analyze multiple pages in batch
        
        Args:
            pages: List of page image data
            artifact_type: 'assertions' or 'covergroups'
            
        Returns:
            List of analysis results
        """
        results = []
        
        for page_data in pages:
            analysis = self.analyze_page_for_relevance(page_data, artifact_type)
            results.append(analysis)
        
        return results


class VisionDocumentProcessor:
    """Main vision-first document processor"""
    
    def __init__(self):
        self.converter = DocumentToImageConverter()
        self.analyzer = VisionPageAnalyzer()
    
    def process_document_with_vision(self, filepath: str, artifact_type: str) -> Dict[str, any]:
        """
        Process document using vision-first approach
        
        Args:
            filepath: Path to document
            artifact_type: 'assertions' or 'covergroups'
            
        Returns:
            Processing results with filtered pages and analysis
        """
        file_ext = Path(filepath).suffix.lower()
        
        # Step 1: Convert to images
        if file_ext == '.pdf':
            pages = self.converter.pdf_to_images(filepath)
        elif file_ext in ['.docx', '.doc']:
            try:
                pages = self.converter.docx_to_images(filepath)
            except:
                # Fallback: extract text and convert to images
                from document_processor import DocumentReader
                text, _ = DocumentReader.read_file(filepath)
                # Split into page-sized chunks
                chunks = [text[i:i+3000] for i in range(0, len(text), 3000)]
                pages = [self.converter.text_to_image(chunk, i+1) for i, chunk in enumerate(chunks)]
        elif file_ext in ['.txt', '.md']:
            from document_processor import DocumentReader
            text, _ = DocumentReader.read_file(filepath)
            # Split into page-sized chunks
            chunks = [text[i:i+3000] for i in range(0, len(text), 3000)]
            pages = [self.converter.text_to_image(chunk, i+1) for i, chunk in enumerate(chunks)]
        else:
            raise ValueError(f"Unsupported file format: {file_ext}")
        
        # Step 2: Vision analysis to score each page
        page_analyses = self.analyzer.batch_analyze_pages(pages, artifact_type)
        
        # Step 3: Filter pages - keep only relevant ones
        relevant_pages = []
        discarded_pages = []
        
        for page_data, analysis in zip(pages, page_analyses):
            if analysis['is_relevant']:
                relevant_pages.append({
                    'page_data': page_data,
                    'analysis': analysis
                })
            else:
                discarded_pages.append({
                    'page_number': page_data['page_number'],
                    'reason': analysis['reasoning']
                })
        
        # Step 4: Prepare filtered images for final processing
        filtered_images = [p['page_data'] for p in relevant_pages]
        
        return {
            'filepath': filepath,
            'file_type': file_ext,
            'total_pages': len(pages),
            'relevant_pages': len(relevant_pages),
            'discarded_pages': len(discarded_pages),
            'artifact_type': artifact_type,
            'page_analyses': page_analyses,
            'filtered_page_data': relevant_pages,
            'filtered_images': filtered_images,
            'discard_info': discarded_pages
        }
    
    def extract_text_from_filtered_pages(self, processing_result: Dict[str, any]) -> str:
        """
        Extract text from filtered pages using OCR or original extraction
        
        Args:
            processing_result: Result from process_document_with_vision
            
        Returns:
            Concatenated text from relevant pages only
        """
        # For now, re-extract from original document using page numbers
        # In production, you'd want to use OCR on the images
        
        filepath = processing_result['filepath']
        relevant_page_nums = [p['page_data']['page_number'] for p in processing_result['filtered_page_data']]
        
        # Extract text from original document, filtered by page numbers
        from document_processor import DocumentReader
        full_text, _ = DocumentReader.read_file(filepath)
        
        # For PDF, extract specific pages
        if filepath.endswith('.pdf'):
            text_parts = []
            with open(filepath, 'rb') as file:
                pdf_reader = PyPDF2.PdfReader(file)
                for page_num in relevant_page_nums:
                    if page_num <= len(pdf_reader.pages):
                        page = pdf_reader.pages[page_num - 1]
                        text_parts.append(page.extract_text())
            
            return "\n\n".join(text_parts)
        else:
            # For other formats, return full text (since we can't easily extract by page)
            return full_text
    
    def prepare_vision_context(self, processing_result: Dict[str, any]) -> str:
        """
        Prepare context for AI agent from vision-filtered results
        
        Args:
            processing_result: Result from process_document_with_vision
            
        Returns:
            Formatted context string
        """
        artifact_type = processing_result['artifact_type']
        
        context = f"""Vision-Filtered Document Analysis for {artifact_type.upper()} Generation
{'='*70}

File: {os.path.basename(processing_result['filepath'])}
Type: {processing_result['file_type']}
Total Pages: {processing_result['total_pages']}
Relevant Pages: {processing_result['relevant_pages']} (kept)
Discarded Pages: {processing_result['discarded_pages']} (filtered out)

Vision filtering has removed {processing_result['discarded_pages']} irrelevant pages,
leaving only {processing_result['relevant_pages']} pages with {artifact_type}-related content.

"""
        
        # Show which pages were kept and why
        context += f"\n📋 RELEVANT PAGES (Vision-Filtered):\n{'─'*70}\n"
        
        for page_info in processing_result['filtered_page_data']:
            analysis = page_info['analysis']
            page_num = analysis['page_number']
            score = analysis['score']
            hints = analysis.get('key_hints', [])
            
            context += f"\nPage {page_num}: Score {score}/10\n"
            if hints:
                context += f"  Key indicators: {', '.join(hints[:5])}\n"
            context += f"  {analysis['reasoning'][:200]}...\n"
        
        # Add extracted text from filtered pages
        context += f"\n{'='*70}\n"
        context += f"FILTERED CONTENT:\n{'='*70}\n\n"
        
        filtered_text = self.extract_text_from_filtered_pages(processing_result)
        context += filtered_text
        
        return context
