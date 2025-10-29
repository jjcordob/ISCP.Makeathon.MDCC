"""
Specialized AI Agents for Verification Artifact Generation
Multiple agents to handle different aspects of verification code generation
"""

from typing import Dict, List, Optional
from config import Config
from openai import AzureOpenAI
import httpx


class BaseVerificationAgent:
    """Base class for verification agents"""
    
    def __init__(self, role: str, expertise: str):
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
        self.role = role
        self.expertise = expertise
        self.conversation_history = []
    
    def is_ready(self) -> bool:
        """Check if agent is configured"""
        return Config.get_api_key_status()
    
    def reset_conversation(self):
        """Reset conversation history"""
        self.conversation_history = []
    
    def get_response(self, user_message: str, system_context: str = "") -> str:
        """
        Get response from AI agent
        
        Args:
            user_message: User's message/request
            system_context: Additional system context
            
        Returns:
            Agent's response
        """
        try:
            # Build system prompt
            system_prompt = f"""You are a {self.role} specialized in {self.expertise}.

{system_context}

CRITICAL OPERATING PRINCIPLES:
1. Work STRICTLY from provided documents/requirements
2. DO NOT add information, assumptions, or industry knowledge not in the input
3. DO NOT invent signals, protocols, or features not mentioned
4. DO NOT add "best practice" elements unless explicitly requested
5. When extracting requirements: be comprehensive but conservative
6. When generating code: implement ONLY what is specified
7. If something is unclear or missing, note it rather than assuming

Your expertise includes:
- Deep understanding of SystemVerilog and verification methodologies
- Ability to extract requirements EXACTLY from specifications
- Creating verification code that matches requirements precisely
- Following industry standards ONLY when explicitly requested

Respond concisely, professionally, and STRICTLY based on provided information."""

            # Build messages
            messages = [{"role": "system", "content": system_prompt}]
            
            # Add conversation history
            messages.extend(self.conversation_history)
            
            # Add current message
            messages.append({"role": "user", "content": user_message})
            
            # Call API
            response = self.client.chat.completions.create(
                model=Config.AZURE_OPENAI_DEPLOYMENT,
                messages=messages,
                temperature=0.3,  # Lower temperature for more focused output
                max_tokens=4000
            )
            
            assistant_message = response.choices[0].message.content
            
            # Update history
            self.conversation_history.append({"role": "user", "content": user_message})
            self.conversation_history.append({"role": "assistant", "content": assistant_message})
            
            return assistant_message
            
        except Exception as e:
            return f"Error: {str(e)}"


class AssertionSpecialist(BaseVerificationAgent):
    """Specialized agent for SVA assertion generation"""
    
    def __init__(self):
        super().__init__(
            role="SystemVerilog Assertion (SVA) Specialist",
            expertise="creating property-based assertions, protocol checkers, and formal verification properties"
        )
    
    def extract_assertion_requirements(self, document_context: str) -> str:
        """
        Extract assertion requirements from document context
        
        Args:
            document_context: Analyzed document sections
            
        Returns:
            Extracted requirements summary
        """
        prompt = """Analyze the following verification specification and extract ALL assertion requirements.

CRITICAL RULES:
1. Extract ONLY information that is EXPLICITLY stated in the document
2. DO NOT add assumptions, interpretations, or best practices not in the document
3. DO NOT invent signals, protocols, or requirements not mentioned
4. If something is unclear or not specified, note it as "Not specified in document"
5. Quote relevant sections when extracting requirements

For each requirement found in the document, identify:
1. What property/behavior needs to be checked (EXACT wording from document)
2. The signals/interfaces involved (ONLY those mentioned in document)
3. Timing relationships (ONLY if specified in document)
4. Any conditional constraints (ONLY if stated in document)
5. Error/success conditions (ONLY from document)

Document Content:
---
{context}
---

Extract and list ALL assertion requirements STRICTLY from the document.
Mark anything not explicitly stated as [NOT SPECIFIED].
Use exact terminology from the document - do not paraphrase unnecessarily.""".format(context=document_context)

        return self.get_response(prompt)
    
    def generate_assertions(self, requirements: str, design_signals: str = "") -> str:
        """
        Generate SVA assertions from requirements
        
        Args:
            requirements: Extracted assertion requirements
            design_signals: Optional design signal information
            
        Returns:
            Generated SystemVerilog assertion code
        """
        signal_context = f"\n\nDesign Signals Available:\n{design_signals}" if design_signals else ""
        
        prompt = f"""Generate SystemVerilog Assertions (SVA) STRICTLY based on these requirements.

Requirements:
---
{requirements}
---
{signal_context}

CRITICAL INSTRUCTIONS - MUST FOLLOW:
1. Generate ONLY SystemVerilog assertion code
2. Use ONLY signals/interfaces explicitly mentioned in the requirements
3. DO NOT add assertions for scenarios not mentioned in requirements
4. DO NOT add "best practice" assertions not requested
5. If requirements mention specific timing (e.g., "within 5 cycles"), use EXACT values
6. If timing is not specified, use reasonable defaults and add comments
7. Wrap code in: ```systemverilog:assertions.sv
8. Include properties, sequences, and assertions
9. Add meaningful assertion names based on requirement descriptions
10. Use proper SVA syntax with temporal operators
11. Include disable conditions where appropriate
12. Add comments explaining what each assertion verifies FROM THE REQUIREMENTS

ENUMERATE ASSERTIONS:
- If requirements are numbered/enumerated (e.g., "REQ-001", "1.", "a)"), preserve that structure
- Name assertions to match requirement IDs: `assert_req_001`, `assert_item_1a`
- Add comments linking each assertion to its requirement number/ID
- Group assertions by requirement sections if document has hierarchical structure

PRESERVE DESCRIPTIONS:
- Copy exact requirement descriptions as comments above each assertion
- If requirement states "The system shall...", include that as comment
- Maintain any priority labels (Critical/High/Medium/Low) in comments
- Include any notes or constraints from the original requirement

Example structure (ONLY if requirements specify similar checks):
```systemverilog:assertions.sv
// REQ-001: Request must be acknowledged within 1-5 cycles
// Priority: Critical
property p_req_001_ack_timing;
    @(posedge clk) disable iff (!rst_n)
    req |-> ##[1:5] ack;
endproperty

assert property (p_req_001_ack_timing) 
    else $error("[REQ-001] Request not acknowledged within 5 cycles");

// REQ-002: Valid signal must remain stable during transfer
// Priority: High
property p_req_002_valid_stable;
    @(posedge clk) disable iff (!rst_n)
    $rose(valid) |-> valid throughout transfer;
endproperty

assert property (p_req_002_valid_stable)
    else $error("[REQ-002] Valid signal changed during transfer");
```

Generate ONLY assertions that directly implement the stated requirements.
DO NOT add extra assertions "for completeness" or "best practices".
PRESERVE all requirement numbering and descriptions.
RETURN ONLY CODE - NO OTHER TEXT."""

        return self.get_response(prompt)


class CoverageSpecialist(BaseVerificationAgent):
    """Specialized agent for functional coverage generation"""
    
    def __init__(self):
        super().__init__(
            role="Functional Coverage Specialist",
            expertise="creating covergroups, coverpoints, cross coverage, and coverage-driven verification strategies"
        )
    
    def extract_coverage_requirements(self, document_context: str) -> str:
        """
        Extract coverage requirements from document context
        
        Args:
            document_context: Analyzed document sections
            
        Returns:
            Extracted coverage requirements
        """
        prompt = """Analyze the following verification specification and extract ALL functional coverage requirements.

CRITICAL RULES:
1. Extract ONLY information that is EXPLICITLY stated in the document
2. DO NOT add coverage points not mentioned in the document
3. DO NOT invent test scenarios or cases not specified
4. DO NOT add "standard" coverage not requested in document
5. If coverage is not specified, note it as "Not specified in document"
6. Quote relevant sections when extracting requirements

For each coverage requirement found in the document, identify:
1. What scenarios/cases need to be covered (EXACT from document)
2. Signal values and ranges to monitor (ONLY those mentioned)
3. State transitions or sequences (ONLY if specified)
4. Corner cases and boundary conditions (ONLY if stated)
5. Cross-coverage between different signals/conditions (ONLY if mentioned)

Document Content:
---
{context}
---

Extract and list ALL coverage requirements STRICTLY from the document.
Mark anything not explicitly stated as [NOT SPECIFIED].
Use exact terminology from the document.""".format(context=document_context)

        return self.get_response(prompt)
    
    def generate_covergroups(self, requirements: str, design_signals: str = "") -> str:
        """
        Generate SystemVerilog covergroups from requirements
        
        Args:
            requirements: Extracted coverage requirements
            design_signals: Optional design signal information
            
        Returns:
            Generated SystemVerilog covergroup code
        """
        signal_context = f"\n\nDesign Signals Available:\n{design_signals}" if design_signals else ""
        
        prompt = f"""Generate SystemVerilog Covergroups STRICTLY based on these requirements.

Requirements:
---
{requirements}
---
{signal_context}

CRITICAL INSTRUCTIONS - MUST FOLLOW:
1. Generate ONLY SystemVerilog covergroup code
2. Create coverpoints ONLY for signals/scenarios mentioned in requirements
3. DO NOT add coverage for signals not mentioned in requirements
4. DO NOT add "typical" bins not specified in requirements
5. If requirements specify value ranges, use EXACT ranges
6. If ranges not specified, add comment noting this
7. DO NOT add cross coverage unless explicitly mentioned in requirements
8. Wrap code in: ```systemverilog:coverage.sv
9. Create comprehensive covergroups with coverpoints
10. Use appropriate sampling events (@posedge clk or as specified)
11. Add meaningful names based on requirement descriptions
12. Add comments explaining what each coverpoint tracks FROM THE REQUIREMENTS

ENUMERATE COVERPOINTS:
- If requirements are numbered (e.g., "TC-001", "Scenario 1", "a)"), preserve that structure
- Name covergroups/coverpoints to match test case IDs: `cg_tc_001`, `cp_scenario_1a`
- Add comments linking each coverpoint to its requirement/test case number
- Group coverpoints by test scenario sections if hierarchical

PRESERVE DESCRIPTIONS:
- Copy exact test case descriptions as comments above coverpoints
- If requirement states "Test scenario: ...", include that as comment
- Maintain priority labels (Critical/High/Medium) in comments
- Include any boundary values or ranges from the original requirement

Example structure (ONLY if requirements specify similar coverage):
```systemverilog:coverage.sv
// TC-001: Monitor opcode values for all operation types
// Priority: Critical
// Values: READ(0), WRITE(1), EXECUTE(2), NOP(3)
covergroup cg_tc_001_opcode @(posedge clk);
    option.per_instance = 1;
    option.comment = "TC-001: Operation coverage";
    
    cp_opcode: coverpoint opcode {{
        bins read    = {{2'b00}};  // READ operation
        bins write   = {{2'b01}};  // WRITE operation
        bins execute = {{2'b10}};  // EXECUTE operation
        bins nop     = {{2'b11}};  // No operation
        option.comment = "TC-001: All operation types";
    }}
endgroup

// TC-002: Monitor state transitions
// Priority: High
// States: IDLE, ACTIVE, WAIT, ERROR
covergroup cg_tc_002_state_transitions @(posedge clk);
    option.per_instance = 1;
    option.comment = "TC-002: State coverage";
    
    cp_current_state: coverpoint current_state {{
        bins idle   = {{IDLE}};
        bins active = {{ACTIVE}};
        bins wait   = {{WAIT}};
        bins error  = {{ERROR}};
        option.comment = "TC-002: Current state";
    }}
    
    cp_state_trans: coverpoint current_state {{
        bins idle_to_active = (IDLE => ACTIVE);
        bins active_to_wait = (ACTIVE => WAIT);
        bins wait_to_idle   = (WAIT => IDLE);
        bins error_recovery = (ERROR => IDLE);
        option.comment = "TC-002: Valid transitions";
    }}
endgroup

// TC-003: Monitor address range coverage
// Priority: Medium
// Range: 0x0000 to 0xFFFF, focus on boundaries
covergroup cg_tc_003_address_range @(posedge clk iff valid);
    option.per_instance = 1;
    
    cp_address: coverpoint address {{
        bins zero     = {{16'h0000}};           // Minimum
        bins low      = {{[16'h0001:16'h3FFF]}}; // Low range
        bins mid      = {{[16'h4000:16'hBFFF]}}; // Middle range
        bins high     = {{[16'hC000:16'hFFFE]}}; // High range
        bins max      = {{16'hFFFF}};           // Maximum
        option.comment = "TC-003: Address ranges";
    }}
endgroup
```

Generate ONLY coverage that directly implements the stated requirements.
DO NOT add extra coverpoints "for completeness" or "best practices".
PRESERVE all test case numbering and descriptions.
RETURN ONLY CODE - NO OTHER TEXT."""

        return self.get_response(prompt)


class RequirementsAnalyzer(BaseVerificationAgent):
    """Agent specialized in analyzing and structuring requirements"""
    
    def __init__(self):
        super().__init__(
            role="Requirements Analysis Expert",
            expertise="extracting, structuring, and categorizing verification requirements from specifications"
        )
    
    def analyze_document(self, document_context: str, artifact_type: str) -> Dict[str, any]:
        """
        Analyze document and structure requirements
        
        Args:
            document_context: Document content to analyze
            artifact_type: 'assertions' or 'covergroups'
            
        Returns:
            Structured analysis results
        """
        artifact_focus = {
            'assertions': 'properties to verify, protocol rules, invariants, and behavioral constraints',
            'covergroups': 'scenarios to cover, test cases, corner cases, and state/value combinations'
        }
        
        focus = artifact_focus.get(artifact_type, 'verification requirements')
        
        prompt = f"""Analyze this verification document and create a structured summary focused on {focus}.

CRITICAL RULES - DOCUMENT-ONLY ANALYSIS:
1. Extract ONLY information explicitly stated in the document
2. DO NOT add industry knowledge, assumptions, or best practices
3. DO NOT invent signals, states, or requirements not mentioned
4. DO NOT fill gaps with "typical" or "standard" interpretations
5. If something is unclear, mark it as "Not specified in document"
6. Use exact terminology and names from the document
7. Quote sections when listing requirements

Document:
---
{document_context}
---

Provide:
1. OVERVIEW: Brief summary of ONLY what the document describes
2. KEY SIGNALS: List ONLY signals/interfaces/variables explicitly mentioned in document
3. REQUIREMENTS: Structured list of {artifact_type} requirements EXACTLY as stated
   - Use bullet points with exact quotes or paraphrases
   - Note anything that is implied but not explicit
4. PRIORITY: Categorize ONLY if document specifies priority (Critical/High/Medium/Low)
   - If not specified, mark as "Priority not specified"
5. DEPENDENCIES: Note ONLY dependencies explicitly mentioned in document

Be thorough but STRICT - extract ALL relevant requirements but ADD NOTHING not in the document."""

        response = self.get_response(prompt)
        
        return {
            'artifact_type': artifact_type,
            'analysis': response,
            'raw_context': document_context
        }


class CodeReviewer(BaseVerificationAgent):
    """Agent specialized in reviewing and improving generated code"""
    
    def __init__(self):
        super().__init__(
            role="Verification Code Reviewer",
            expertise="reviewing SVA assertions and covergroups for correctness, completeness, and best practices"
        )
    
    def review_code(self, generated_code: str, requirements: str, artifact_type: str) -> str:
        """
        Review generated verification code
        
        Args:
            generated_code: Generated SVA/coverage code
            requirements: Original requirements
            artifact_type: 'assertions' or 'covergroups'
            
        Returns:
            Review feedback and suggestions
        """
        prompt = f"""Review this generated {artifact_type} code against the requirements.

CRITICAL REVIEW CRITERIA:
1. FIDELITY: Does code match ONLY what's in requirements? (No extra features)
2. COMPLETENESS: Are all stated requirements covered?
3. ACCURACY: Are signal names, values, and timing from requirements used correctly?
4. NO HALLUCINATION: Flag any code elements not based on requirements
5. ENUMERATION: Are requirement IDs/numbers preserved in code (REQ-001, TC-001, etc.)?
6. DESCRIPTIONS: Are original requirement descriptions included as comments?

Requirements:
---
{requirements}
---

Generated Code:
---
{generated_code}
---

Provide feedback on:
1. CORRECTNESS: Is the code syntactically correct?
2. REQUIREMENTS MATCH: Does each code element map to a specific requirement?
3. ENUMERATION PRESERVATION: Are requirement IDs used in names/comments?
4. DESCRIPTION ACCURACY: Are original descriptions preserved as comments?
5. EXTRA CODE: Flag any assertions/coverpoints not in requirements
6. MISSING: What requirements are not addressed?
7. ACCURACY: Are names, values, timing from requirements used exactly?
8. IMPROVEMENTS: Suggest changes ONLY for better matching requirements

Be specific and strict - code should implement ONLY what requirements specify."""

        return self.get_response(prompt)
    
    def refine_code(self, original_code: str, review_feedback: str) -> str:
        """
        Refine code based on review feedback
        
        Args:
            original_code: Original generated code
            review_feedback: Review feedback
            
        Returns:
            Improved code
        """
        prompt = f"""Improve this code based on the review feedback.

CRITICAL INSTRUCTIONS:
1. Fix ONLY issues identified in the feedback
2. DO NOT add features not mentioned in feedback
3. DO NOT add "improvements" beyond what feedback suggests
4. If feedback says "extra code", REMOVE it
5. If feedback says "missing requirement", ADD it
6. If feedback mentions missing enumeration/IDs, ADD them
7. If feedback mentions missing descriptions, ADD them as comments
8. Keep the same code block format
9. Maintain signal names and values as specified

Original Code:
---
{original_code}
---

Review Feedback:
---
{review_feedback}
---

Apply ONLY the changes suggested in feedback.
Return ONLY the improved code - NO explanations outside code blocks.
Do not add anything not explicitly requested in the feedback."""

        return self.get_response(prompt)


class SystemVerilogExpert(BaseVerificationAgent):
    """Expert SystemVerilog/UVM/OVM reviewer for production-quality code"""
    
    def __init__(self):
        super().__init__(
            role="Senior SystemVerilog/UVM Design and Verification Expert",
            expertise="""SystemVerilog language expert with deep knowledge of:
- SystemVerilog Assertions (SVA) - temporal logic, sequences, properties
- Functional Coverage - covergroups, coverpoints, bins, cross coverage
- UVM/OVM methodology - testbench architecture, components, sequences
- RTL design best practices - coding style, synthesis, timing
- Industry standards - IEEE 1800, UVM cookbook, verification guidelines"""
        )
    
    def expert_review(self, code: str, artifact_type: str, requirements: str = "") -> str:
        """
        Expert review of SystemVerilog code for production quality
        
        Args:
            code: Generated SystemVerilog code
            artifact_type: 'assertions', 'covergroups', 'rtl', or 'uvm'
            requirements: Optional requirements context
            
        Returns:
            Expert review with specific improvement suggestions
        """
        req_context = f"\n\nOriginal Requirements:\n{requirements}" if requirements else ""
        
        prompt = f"""As a Senior SystemVerilog/UVM Expert, perform a detailed technical review of this code.

Code Type: {artifact_type.upper()}
---
{code}
---
{req_context}

EXPERT REVIEW CRITERIA:

1. SYNTAX & SEMANTICS:
   - Correct SystemVerilog syntax (IEEE 1800 compliant)?
   - Proper use of data types, operators, and constructs?
   - No syntax errors or warnings?

2. SVA BEST PRACTICES (if assertions):
   - Proper use of temporal operators (##, |->", |=>)?
   - Correct sequence and property definitions?
   - Appropriate disable conditions?
   - Meaningful error messages with context?
   - Proper clock and reset handling?
   - No race conditions or sampling issues?

3. COVERAGE BEST PRACTICES (if covergroups):
   - Appropriate sampling events and conditions?
   - Correct bin definitions and ranges?
   - Meaningful option settings (per_instance, at_least, etc.)?
   - Cross coverage only where needed?
   - Illegal/ignore bins for invalid cases?
   - Transition bins for state machines?

4. NAMING CONVENTIONS:
   - Clear, descriptive names following conventions?
   - Assertions: p_* for properties, seq_* for sequences, assert_* or a_* for assertions?
   - Coverage: cg_* for covergroups, cp_* for coverpoints?
   - Consistent naming scheme throughout?

5. COMMENTS & DOCUMENTATION:
   - Adequate comments explaining intent?
   - Requirement IDs preserved and linked?
   - Complex logic well documented?
   - Header comments for main constructs?

6. CODE ORGANIZATION:
   - Logical grouping of related items?
   - Consistent formatting and indentation?
   - Reusable sequences/properties where appropriate?
   - No code duplication?

7. VERIFICATION COMPLETENESS:
   - All requirements addressed?
   - Corner cases considered?
   - Appropriate error checking?
   - No over-specification (extra code not in requirements)?

8. PRODUCTION READINESS:
   - Suitable for use in real verification environment?
   - Portable and maintainable?
   - Performance considerations?
   - Synthesis implications (if RTL)?

PROVIDE:
- SCORE: X/10 for production readiness
- STRENGTHS: What is done well
- ISSUES: Specific problems found (with line references if possible)
- IMPROVEMENTS: Concrete suggestions for enhancement
- BEST PRACTICES: Industry best practices to apply
- OPTIONAL ENHANCEMENTS: Nice-to-have improvements (clearly marked as optional)

Be thorough but constructive. Focus on actionable feedback."""

        return self.get_response(prompt)
    
    def improve_code(self, code: str, expert_review: str, artifact_type: str) -> str:
        """
        Improve code based on expert review
        
        Args:
            code: Original code
            expert_review: Expert review feedback
            artifact_type: Code type
            
        Returns:
            Improved production-quality code
        """
        prompt = f"""As a SystemVerilog/UVM Expert, improve this code based on the expert review.

Original Code:
---
{code}
---

Expert Review:
---
{expert_review}
---

IMPROVEMENT GUIDELINES:
1. Fix ALL issues identified in the review
2. Apply BEST PRACTICES mentioned
3. DO NOT apply OPTIONAL ENHANCEMENTS unless they directly address issues
4. Maintain requirement fidelity - don't add functionality not in original
5. Use proper SystemVerilog style and conventions
6. Add/improve comments as suggested
7. Preserve all requirement IDs and descriptions
8. Return ONLY code in proper format: ```systemverilog:filename.sv

Generate the improved, production-quality code.
NO explanations outside code blocks."""

        return self.get_response(prompt)
