"""
AI-Powered Section Validator
Uses AI to validate and re-rank document sections for better accuracy
"""

from typing import Dict, List
from src.config import Config
from openai import AzureOpenAI
import httpx


class AIValidator:
    """Uses AI to validate section relevance and extract structured information"""
    
    def __init__(self):
        """Initialize the AI validator"""
        # Configure HTTP client with proxy
        http_client = httpx.Client(
            verify=False,
            proxy="http://proxy-chain.intel.com:911"
        )
        
        self.client = AzureOpenAI(
            api_key=Config.AZURE_OPENAI_KEY,
            api_version=Config.AZURE_OPENAI_API_VERSION,
            azure_endpoint=Config.AZURE_OPENAI_ENDPOINT,
            http_client=http_client
        )
    
    def validate_section_relevance(self, section_text: str, section_title: str, 
                                   artifact_type: str) -> Dict[str, any]:
        """
        Use AI to validate if a section is truly relevant
        
        Args:
            section_text: Section content
            section_title: Section title
            artifact_type: 'assertions' or 'covergroups'
            
        Returns:
            Validation result with score and explanation
        """
        artifact_desc = {
            'assertions': 'SystemVerilog assertions (SVA), properties, protocol checking, or verification requirements',
            'covergroups': 'functional coverage, covergroups, test scenarios, or coverage requirements'
        }
        
        prompt = f"""Analyze this document section and determine its relevance for generating {artifact_desc.get(artifact_type, artifact_type)}.

Section Title: {section_title}

Section Content:
{section_text[:1500]}

Rate the relevance on a scale of 0-10 where:
- 0-2: Not relevant (no useful information)
- 3-4: Slightly relevant (minimal information)
- 5-6: Moderately relevant (some useful information)
- 7-8: Very relevant (good information)
- 9-10: Highly relevant (excellent, detailed information)

Respond with ONLY a JSON object in this exact format:
{{"relevance_score": <0-10>, "reason": "<brief explanation>", "key_findings": ["<finding1>", "<finding2>"]}}"""

        try:
            response = self.client.chat.completions.create(
                model=Config.AZURE_OPENAI_DEPLOYMENT,
                messages=[
                    {"role": "system", "content": "You are an expert verification engineer analyzing documents for relevance."},
                    {"role": "user", "content": prompt}
                ],
                temperature=0.2,
                max_tokens=300
            )
            
            result_text = response.choices[0].message.content.strip()
            
            # Parse JSON response
            import json
            try:
                result = json.loads(result_text)
                return {
                    'ai_score': result.get('relevance_score', 0) / 10.0,  # Normalize to 0-1
                    'reason': result.get('reason', ''),
                    'key_findings': result.get('key_findings', [])
                }
            except json.JSONDecodeError:
                # Fallback if JSON parsing fails
                return {
                    'ai_score': 0.5,
                    'reason': 'Could not parse AI response',
                    'key_findings': []
                }
                
        except Exception as e:
            return {
                'ai_score': 0.5,
                'reason': f'Error: {str(e)}',
                'key_findings': []
            }
    
    def validate_and_rerank_sections(self, sections: List[Dict[str, any]], 
                                    artifact_type: str,
                                    max_validate: int = 10) -> List[Dict[str, any]]:
        """
        Validate top sections with AI and re-rank based on combined scores
        
        Args:
            sections: List of sections with keyword-based scores
            artifact_type: Type of artifact to generate
            max_validate: Maximum number of sections to validate with AI
            
        Returns:
            Re-ranked sections with AI validation
        """
        # Only validate top sections (AI is expensive)
        sections_to_validate = sections[:max_validate]
        
        for section_data in sections_to_validate:
            chunk = section_data['chunk']
            
            # Get AI validation
            validation = self.validate_section_relevance(
                chunk['content'],
                chunk['title'],
                artifact_type
            )
            
            # Combine keyword score with AI score (weighted average)
            keyword_score = section_data['score']
            ai_score = validation['ai_score']
            
            # 60% keyword-based, 40% AI-based
            combined_score = (keyword_score * 0.6) + (ai_score * 0.4)
            
            section_data['ai_validation'] = validation
            section_data['original_score'] = keyword_score
            section_data['score'] = combined_score
        
        # Re-sort by combined score
        sections.sort(key=lambda x: x['score'], reverse=True)
        
        return sections
