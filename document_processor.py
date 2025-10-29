"""
Document Processor for DVM
Handles PDF, DOCX, MD, and TXT files to extract verification requirements
"""

import os
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple
import PyPDF2
from docx import Document
import markdown


class DocumentReader:
    """Reads and extracts text from various document formats"""
    
    @staticmethod
    def read_file(filepath: str) -> Tuple[str, str]:
        """
        Read file and return content with format type
        
        Args:
            filepath: Path to the document
            
        Returns:
            Tuple of (content, file_type)
        """
        file_ext = Path(filepath).suffix.lower()
        
        if file_ext == '.pdf':
            return DocumentReader.read_pdf(filepath), 'pdf'
        elif file_ext in ['.docx', '.doc']:
            return DocumentReader.read_docx(filepath), 'docx'
        elif file_ext == '.md':
            return DocumentReader.read_markdown(filepath), 'markdown'
        elif file_ext == '.txt':
            return DocumentReader.read_txt(filepath), 'txt'
        else:
            raise ValueError(f"Unsupported file format: {file_ext}")
    
    @staticmethod
    def read_pdf(filepath: str) -> str:
        """Extract text from PDF file"""
        try:
            with open(filepath, 'rb') as file:
                pdf_reader = PyPDF2.PdfReader(file)
                text = ""
                for page in pdf_reader.pages:
                    text += page.extract_text() + "\n\n"
                return text.strip()
        except Exception as e:
            raise Exception(f"Error reading PDF: {str(e)}")
    
    @staticmethod
    def read_docx(filepath: str) -> str:
        """Extract text from DOCX file"""
        try:
            doc = Document(filepath)
            paragraphs = [para.text for para in doc.paragraphs]
            return "\n".join(paragraphs)
        except Exception as e:
            raise Exception(f"Error reading DOCX: {str(e)}")
    
    @staticmethod
    def read_markdown(filepath: str) -> str:
        """Read markdown file (keep as plain text)"""
        try:
            with open(filepath, 'r', encoding='utf-8') as file:
                return file.read()
        except Exception as e:
            raise Exception(f"Error reading Markdown: {str(e)}")
    
    @staticmethod
    def read_txt(filepath: str) -> str:
        """Read plain text file"""
        try:
            with open(filepath, 'r', encoding='utf-8') as file:
                return file.read()
        except Exception as e:
            raise Exception(f"Error reading TXT: {str(e)}")


class DocumentChunker:
    """Splits document into manageable chunks for processing"""
    
    @staticmethod
    def extract_header_hierarchy(line: str, prev_line: str = "") -> Tuple[Optional[str], int, str]:
        """
        Extract header text, level, and type from a line
        
        Args:
            line: Current line to check
            prev_line: Previous line (for underline-style headers)
            
        Returns:
            Tuple of (header_text, level, header_type) or (None, 0, "") if not a header
        """
        line_stripped = line.strip()
        
        # Markdown headers: # Header, ## Header, etc.
        md_match = re.match(r'^(#{1,6})\s+(.+)$', line_stripped)
        if md_match:
            level = len(md_match.group(1))
            return md_match.group(2).strip(), level, 'markdown'
        
        # Underline-style headers (setext)
        if prev_line.strip():
            if re.match(r'^[=]{3,}$', line_stripped):  # === underline
                return prev_line.strip(), 1, 'setext-h1'
            elif re.match(r'^[-]{3,}$', line_stripped):  # --- underline
                return prev_line.strip(), 2, 'setext-h2'
        
        # Numbered sections: 1. Header, 2.3 Header, etc.
        num_match = re.match(r'^(\d+(?:\.\d+)*)\.\s+(.+)$', line_stripped)
        if num_match:
            level = len(num_match.group(1).split('.'))
            return num_match.group(2).strip(), level, 'numbered'
        
        # ALL CAPS headers (must be 4+ words and all uppercase)
        if len(line_stripped) > 10 and line_stripped.isupper() and len(line_stripped.split()) >= 2:
            return line_stripped, 2, 'caps'
        
        # Section/Chapter headers
        section_match = re.match(r'^(Section|Chapter|Part|Appendix)\s+(\d+|[A-Z]):?\s*(.*)$', line_stripped, re.IGNORECASE)
        if section_match:
            title = f"{section_match.group(1)} {section_match.group(2)}"
            if section_match.group(3):
                title += f": {section_match.group(3)}"
            return title, 1, 'section'
        
        return None, 0, ""
    
    @staticmethod
    def chunk_by_sections(text: str, max_chunk_size: int = 3000) -> List[Dict[str, str]]:
        """
        Split document into logical sections with enhanced header detection
        
        Args:
            text: Full document text
            max_chunk_size: Maximum characters per chunk
            
        Returns:
            List of chunks with metadata including header hierarchy
        """
        chunks = []
        lines = text.split('\n')
        
        current_section = {
            "title": "Document Start",
            "content": "",
            "start_line": 0,
            "header_level": 0,
            "header_type": "default",
            "parent_headers": []  # Track hierarchical context
        }
        
        header_stack = []  # Stack to track header hierarchy
        prev_line = ""
        skip_next = False  # For underline-style headers
        
        for i, line in enumerate(lines):
            if skip_next:
                skip_next = False
                continue
            
            # Check if line is a header
            header_text, level, header_type = DocumentChunker.extract_header_hierarchy(line, prev_line)
            
            if header_text:
                # Handle underline-style headers
                if header_type.startswith('setext'):
                    skip_next = True
                
                # Save previous section if it has content
                if current_section["content"].strip():
                    chunks.append(current_section)
                
                # Update header stack for hierarchy
                while header_stack and header_stack[-1]['level'] >= level:
                    header_stack.pop()
                
                # Build parent headers path
                parent_headers = [h['title'] for h in header_stack]
                
                # Add current header to stack
                header_stack.append({'title': header_text, 'level': level})
                
                # Start new section
                current_section = {
                    "title": header_text,
                    "content": "",
                    "start_line": i,
                    "header_level": level,
                    "header_type": header_type,
                    "parent_headers": parent_headers.copy(),
                    "full_path": " > ".join(parent_headers + [header_text]) if parent_headers else header_text
                }
            else:
                current_section["content"] += line + "\n"
            
            # Split large sections while preserving hierarchy
            if len(current_section["content"]) > max_chunk_size:
                chunks.append(current_section)
                parent_headers = current_section.get("parent_headers", [])
                current_section = {
                    "title": f"{current_section['title']} (continued)",
                    "content": "",
                    "start_line": i,
                    "header_level": current_section.get("header_level", 0),
                    "header_type": current_section.get("header_type", "default"),
                    "parent_headers": parent_headers,
                    "full_path": current_section.get("full_path", "") + " (cont.)"
                }
            
            prev_line = line
        
        # Add last section
        if current_section["content"].strip():
            chunks.append(current_section)
        
        return chunks
    
    @staticmethod
    def chunk_by_paragraphs(text: str, max_chunk_size: int = 2000) -> List[Dict[str, str]]:
        """
        Split document by paragraphs when no clear sections exist
        
        Args:
            text: Full document text
            max_chunk_size: Maximum characters per chunk
            
        Returns:
            List of chunks with metadata
        """
        chunks = []
        paragraphs = text.split('\n\n')
        
        current_chunk = {"title": f"Chunk 1", "content": "", "start_para": 0}
        chunk_num = 1
        
        for i, para in enumerate(paragraphs):
            if len(current_chunk["content"]) + len(para) > max_chunk_size:
                chunks.append(current_chunk)
                chunk_num += 1
                current_chunk = {
                    "title": f"Chunk {chunk_num}",
                    "content": para + "\n\n",
                    "start_para": i
                }
            else:
                current_chunk["content"] += para + "\n\n"
        
        if current_chunk["content"].strip():
            chunks.append(current_chunk)
        
        return chunks


class SectionAnalyzer:
    """Analyzes document sections to find relevant verification content"""
    
    # Enhanced keywords with weights for different verification artifacts
    ASSERTION_KEYWORDS = {
        # High priority - direct assertion indicators (weight: 3)
        'assertion': 3, 'assert': 3, 'property': 3, 'sva': 3, 'formal': 3,
        'checker': 3, 'protocol': 3, 'invariant': 3,
        
        # Medium priority - requirement indicators (weight: 2)
        'must': 2, 'shall': 2, 'requirement': 2, 'verify': 2, 'check': 2,
        'validate': 2, 'ensure': 2, 'guarantee': 2, 'constraint': 2,
        
        # Low priority - general verification terms (weight: 1)
        'should': 1, 'always': 1, 'never': 1, 'rule': 1, 'condition': 1,
        'assume': 1, 'sequence': 1, 'temporal': 1, 'safety': 1, 'liveness': 1
    }
    
    COVERGROUP_KEYWORDS = {
        # High priority - direct coverage indicators (weight: 3)
        'coverage': 3, 'coverpoint': 3, 'covergroup': 3, 'bins': 3,
        'cross coverage': 3, 'functional coverage': 3, 'code coverage': 3,
        
        # Medium priority - scenario indicators (weight: 2)
        'scenario': 2, 'test case': 2, 'corner case': 2, 'edge case': 2,
        'boundary': 2, 'transition': 2, 'state': 2, 'combination': 2,
        
        # Low priority - general testing terms (weight: 1)
        'case': 1, 'condition': 1, 'value': 1, 'range': 1, 'sequence': 1,
        'event': 1, 'monitor': 1, 'observe': 1, 'track': 1
    }
    
    # Signal/interface keywords that boost relevance
    DESIGN_KEYWORDS = {
        'signal': 2, 'interface': 2, 'port': 2, 'clock': 2, 'reset': 2,
        'input': 1, 'output': 1, 'register': 1, 'wire': 1, 'bus': 1,
        'handshake': 2, 'valid': 1, 'ready': 1, 'enable': 1, 'request': 2,
        'acknowledge': 2, 'data': 1, 'address': 1, 'control': 1
    }
    
    @staticmethod
    def score_section_for_assertions(chunk: Dict[str, str]) -> float:
        """
        Score a section for assertion-related content with weighted keywords
        
        Args:
            chunk: Document chunk with title and content
            
        Returns:
            Relevance score (0.0 to 1.0)
        """
        text = chunk['content'].lower()
        title = chunk['title'].lower()
        
        # Calculate weighted keyword score
        keyword_score = 0
        total_words = len(text.split())
        
        if total_words == 0:
            return 0.0
        
        # Score assertion keywords with weights
        for keyword, weight in SectionAnalyzer.ASSERTION_KEYWORDS.items():
            count = len(re.findall(r'\b' + keyword + r'\b', text))
            keyword_score += count * weight
        
        # Boost for design-related keywords (indicates technical content)
        design_boost = 0
        for keyword, weight in SectionAnalyzer.DESIGN_KEYWORDS.items():
            count = len(re.findall(r'\b' + keyword + r'\b', text))
            design_boost += count * weight * 0.5  # Half weight for design terms
        
        # Title boost - if title contains relevant keywords, increase score
        title_boost = 1.0
        for keyword in SectionAnalyzer.ASSERTION_KEYWORDS.keys():
            if keyword in title:
                title_boost = 2.0
                break
        
        # Check for requirement patterns (e.g., "REQ-001", "Requirement 1.2.3")
        requirement_pattern = r'\b(req|requirement|spec)[-\s]?\d+\.?\d*\b'
        requirement_matches = len(re.findall(requirement_pattern, text, re.IGNORECASE))
        requirement_boost = min(requirement_matches * 0.1, 0.5)  # Cap at 0.5
        
        # Check for shall/must statements (strong requirement indicators)
        strong_requirement_pattern = r'\b(shall|must)\s+\w+'
        strong_matches = len(re.findall(strong_requirement_pattern, text, re.IGNORECASE))
        strong_boost = min(strong_matches * 0.05, 0.3)  # Cap at 0.3
        
        # Calculate final score
        base_score = (keyword_score + design_boost) / total_words * 100
        final_score = base_score * title_boost + requirement_boost + strong_boost
        
        # Normalize to 0-1 range
        return min(1.0, final_score)
    
    @staticmethod
    def score_section_for_covergroups(chunk: Dict[str, str]) -> float:
        """
        Score a section for covergroup-related content with weighted keywords
        
        Args:
            chunk: Document chunk with title and content
            
        Returns:
            Relevance score (0.0 to 1.0)
        """
        text = chunk['content'].lower()
        title = chunk['title'].lower()
        
        # Calculate weighted keyword score
        keyword_score = 0
        total_words = len(text.split())
        
        if total_words == 0:
            return 0.0
        
        # Score coverage keywords with weights
        for keyword, weight in SectionAnalyzer.COVERGROUP_KEYWORDS.items():
            count = len(re.findall(r'\b' + keyword + r'\b', text))
            keyword_score += count * weight
        
        # Boost for design-related keywords
        design_boost = 0
        for keyword, weight in SectionAnalyzer.DESIGN_KEYWORDS.items():
            count = len(re.findall(r'\b' + keyword + r'\b', text))
            design_boost += count * weight * 0.5
        
        # Title boost
        title_boost = 1.0
        for keyword in SectionAnalyzer.COVERGROUP_KEYWORDS.keys():
            if keyword in title:
                title_boost = 2.0
                break
        
        # Check for test case patterns
        test_case_pattern = r'\b(test\s+case|tc[-_]?\d+|scenario[-_]?\d+)\b'
        test_matches = len(re.findall(test_case_pattern, text, re.IGNORECASE))
        test_boost = min(test_matches * 0.1, 0.4)
        
        # Check for value/range specifications (e.g., "0-255", "valid values")
        range_pattern = r'\b\d+\s*[-to]+\s*\d+\b'
        range_matches = len(re.findall(range_pattern, text))
        range_boost = min(range_matches * 0.05, 0.2)
        
        # Calculate final score
        base_score = (keyword_score + design_boost) / total_words * 100
        final_score = base_score * title_boost + test_boost + range_boost
        
        # Normalize to 0-1 range
        return min(1.0, final_score)
    
    @staticmethod
    def extract_key_entities(text: str) -> Dict[str, List[str]]:
        """
        Extract key entities from text (signals, states, values)
        
        Args:
            text: Text to analyze
            
        Returns:
            Dictionary of entity types and their instances
        """
        entities = {
            'signals': [],
            'states': [],
            'values': [],
            'operations': []
        }
        
        # Extract signal names (common patterns: sig_name, signalName, SIGNAL_NAME)
        signal_pattern = r'\b[a-z_][a-z0-9_]*(?:_(?:sig|signal|port|bus|wire|reg))?\b'
        potential_signals = re.findall(signal_pattern, text.lower())
        entities['signals'] = list(set([s for s in potential_signals if len(s) > 2]))[:10]
        
        # Extract state names (STATE_X, idle_state, etc.)
        state_pattern = r'\b(?:state_)?(?:idle|active|busy|ready|wait|done|error|init|reset)\b'
        entities['states'] = list(set(re.findall(state_pattern, text.lower())))[:10]
        
        # Extract numeric values and ranges
        value_pattern = r'\b(?:0x[0-9a-f]+|\d+(?:\.\d+)?)\b'
        entities['values'] = list(set(re.findall(value_pattern, text.lower())))[:10]
        
        # Extract operations (read, write, send, receive, etc.)
        operation_pattern = r'\b(read|write|send|receive|transmit|transfer|set|clear|enable|disable)\b'
        entities['operations'] = list(set(re.findall(operation_pattern, text.lower())))
        
        return entities
    
    @staticmethod
    def find_relevant_sections(chunks: List[Dict[str, str]], 
                              artifact_type: str,
                              top_n: int = 5,
                              min_score: float = 0.1) -> List[Dict[str, any]]:
        """
        Find most relevant sections with enhanced scoring and entity extraction
        
        Args:
            chunks: List of document chunks
            artifact_type: 'assertions' or 'covergroups'
            top_n: Number of top sections to return
            min_score: Minimum score threshold
            
        Returns:
            List of scored sections sorted by relevance
        """
        scored_sections = []
        
        for chunk in chunks:
            if artifact_type == 'assertions':
                score = SectionAnalyzer.score_section_for_assertions(chunk)
            elif artifact_type == 'covergroups':
                score = SectionAnalyzer.score_section_for_covergroups(chunk)
            else:
                score = 0.0
            
            # Extract key entities from high-scoring sections
            entities = {}
            if score > min_score:
                entities = SectionAnalyzer.extract_key_entities(chunk['content'])
            
            scored_sections.append({
                'chunk': chunk,
                'score': score,
                'entities': entities,
                'word_count': len(chunk['content'].split())
            })
        
        # Sort by score descending
        scored_sections.sort(key=lambda x: x['score'], reverse=True)
        
        # Return top N sections with score > min_score
        return [s for s in scored_sections[:top_n] if s['score'] > min_score]


class DocumentProcessor:
    """Main processor coordinating document analysis"""
    
    def __init__(self):
        self.reader = DocumentReader()
        self.chunker = DocumentChunker()
        self.analyzer = SectionAnalyzer()
    
    def process_document(self, filepath: str, artifact_type: str) -> Dict[str, any]:
        """
        Process document to extract verification requirements
        
        Args:
            filepath: Path to document
            artifact_type: 'assertions' or 'covergroups'
            
        Returns:
            Processing results with relevant sections
        """
        # Step 1: Read document
        content, file_type = self.reader.read_file(filepath)
        
        # Step 2: Chunk into sections
        chunks = self.chunker.chunk_by_sections(content)
        
        # If no clear sections, chunk by paragraphs
        if len(chunks) <= 1:
            chunks = self.chunker.chunk_by_paragraphs(content)
        
        # Step 3: Analyze and find relevant sections
        relevant_sections = self.analyzer.find_relevant_sections(chunks, artifact_type)
        
        # Step 4: Prepare summary
        result = {
            'filepath': filepath,
            'file_type': file_type,
            'total_chunks': len(chunks),
            'artifact_type': artifact_type,
            'relevant_sections': relevant_sections,
            'full_content': content  # Keep full content for reference
        }
        
        return result
    
    def prepare_context_for_agent(self, processing_result: Dict[str, any]) -> str:
        """
        Prepare focused context for AI agent with enhanced metadata and header hierarchy
        
        Args:
            processing_result: Result from process_document
            
        Returns:
            Formatted context string for AI agent with hierarchical organization
        """
        artifact_type = processing_result['artifact_type']
        sections = processing_result['relevant_sections']
        
        context = f"""Document Analysis for {artifact_type.upper()} Generation
{'='*70}

File: {os.path.basename(processing_result['filepath'])}
Type: {processing_result['file_type']}
Total Sections: {processing_result['total_chunks']}
Relevant Sections Found: {len(sections)}

"""
        
        if not sections:
            context += "⚠️  No highly relevant sections found. Analyzing full document.\n\n"
            context += "FULL DOCUMENT CONTENT:\n"
            context += "="*70 + "\n"
            context += processing_result['full_content'][:8000]  # Increased to 8000 chars
            if len(processing_result['full_content']) > 8000:
                context += f"\n\n... (truncated {len(processing_result['full_content']) - 8000} characters)"
        else:
            context += "📋 MOST RELEVANT SECTIONS (Sorted by Relevance):\n"
            context += "   Header hierarchy helps locate information in the original document.\n\n"
            
            for i, section_data in enumerate(sections, 1):
                chunk = section_data['chunk']
                score = section_data['score']
                entities = section_data.get('entities', {})
                word_count = section_data.get('word_count', 0)
                
                context += f"{'─'*70}\n"
                
                # Display hierarchical path if available
                if chunk.get('full_path'):
                    context += f"📍 Location: {chunk['full_path']}\n"
                elif chunk.get('parent_headers'):
                    parent_path = " > ".join(chunk['parent_headers'])
                    context += f"📍 Location: {parent_path} > {chunk['title']}\n"
                else:
                    context += f"📍 Section: {chunk['title']}\n"
                
                # Display header metadata
                header_info = []
                if chunk.get('header_level'):
                    header_info.append(f"Level {chunk['header_level']}")
                if chunk.get('header_type'):
                    header_info.append(f"Type: {chunk['header_type']}")
                if header_info:
                    context += f"   ({', '.join(header_info)})\n"
                
                context += f"Relevance Score: {score:.2%} | Words: {word_count}\n"
                
                # Add extracted entities if available
                if entities:
                    entity_parts = []
                    if entities.get('signals'):
                        entity_parts.append(f"🔌 Signals: {', '.join(entities['signals'][:5])}")
                    if entities.get('states'):
                        entity_parts.append(f"📍 States: {', '.join(entities['states'][:5])}")
                    if entities.get('operations'):
                        entity_parts.append(f"⚙️  Operations: {', '.join(entities['operations'][:5])}")
                    
                    if entity_parts:
                        context += "\n".join(entity_parts) + "\n"
                
                context += f"{'─'*70}\n"
                context += f"{chunk['content']}\n\n"
            
            # Add summary of all extracted entities
            all_signals = set()
            all_states = set()
            all_operations = set()
            
            for section_data in sections:
                entities = section_data.get('entities', {})
                all_signals.update(entities.get('signals', []))
                all_states.update(entities.get('states', []))
                all_operations.update(entities.get('operations', []))
            
            if all_signals or all_states or all_operations:
                context += f"\n{'='*70}\n"
                context += "📊 EXTRACTED DESIGN ELEMENTS SUMMARY:\n"
                context += f"{'='*70}\n"
                if all_signals:
                    context += f"Signals/Ports: {', '.join(list(all_signals)[:15])}\n"
                if all_states:
                    context += f"States: {', '.join(list(all_states)[:10])}\n"
                if all_operations:
                    context += f"Operations: {', '.join(list(all_operations)[:10])}\n"
                context += "\n"
            
            # Add document structure overview
            context += f"{'='*70}\n"
            context += "📑 DOCUMENT STRUCTURE OVERVIEW:\n"
            context += f"{'='*70}\n"
            context += "This shows the organizational structure of the source document.\n"
            context += "Use section headers as hints to understand context and relationships.\n\n"
            
            # Group sections by their parent headers to show structure
            structure_map = {}
            for section_data in sections:
                chunk = section_data['chunk']
                parent_path = " > ".join(chunk.get('parent_headers', []))
                if parent_path not in structure_map:
                    structure_map[parent_path] = []
                structure_map[parent_path].append(chunk['title'])
            
            for parent, titles in structure_map.items():
                if parent:
                    context += f"  {parent}\n"
                    for title in titles:
                        context += f"    └─ {title}\n"
                else:
                    for title in titles:
                        context += f"  • {title}\n"
            context += "\n"
        
        return context
