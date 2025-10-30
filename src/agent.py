"""
AI Agent for DVA (Design Verification Alchemist) application
Handles interactions with Azure OpenAI for RTL and verification code transmutation
"""

from openai import AzureOpenAI
from src.config import Config
import os
import httpx


class DVAAgent:
    """AI Agent for transmuting diagrams and notes to RTL/verification code"""
    
    def __init__(self):
        """Initialize the AI agent"""
        self.client = None
        self.conversation_history = []
        self.system_prompt = self._build_system_prompt()
        
        # Initialize client if API key is available
        if Config.get_api_key_status():
            # Configure HTTP client with proxy if available
            http_client = None
            if Config.HTTP_PROXY:
                http_client = httpx.Client(
                    proxy=Config.HTTP_PROXY,
                    verify=False
                )
            else:
                http_client = httpx.Client(verify=False)
            
            self.client = AzureOpenAI(
                api_key=Config.AZURE_OPENAI_KEY,
                api_version=Config.AZURE_OPENAI_API_VERSION,
                azure_endpoint=Config.AZURE_OPENAI_ENDPOINT,
                http_client=httpx.Client(verify=False,proxy="http://proxy-chain.intel.com:911")
 ,
            )
        
    def _build_system_prompt(self):
        """Build the system prompt for the AI agent"""
        return """You are an expert AI assistant specializing in digital design and hardware verification. Your name is DVA (Design Verification Alchemist).

⚗️ ALCHEMY POWERS - Transmutation capabilities:
1. Hand-drawn notes on paper → RTL code (Verilog/SystemVerilog/VHDL)
2. Block diagrams, state machines, timing diagrams → Synthesizable hardware
3. Test scenarios and requirements → Verification environments (assertions, covergroups, checkers, UVM)
4. Whiteboard sketches → Complete testbench architectures

Like a true alchemist, you follow the law of equivalent exchange: Quality input yields quality output.

When generating RTL code:
- Follow industry-standard coding practices
- Include proper comments and documentation
- Ensure code is synthesizable and follows naming conventions
- Optimize for performance and readability

When generating verification code:
- Create comprehensive testbenches with stimulus generation
- Include assertions for protocol checking
- Generate covergroups for functional coverage
- Implement checkers for design validation

When you receive images of diagrams or notes:
- Analyze the content carefully
- Ask clarifying questions if needed
- Provide well-structured, production-ready code
- Explain the generated code and its functionality

Always be helpful, clear, and professional in your responses."""

    def is_ready(self):
        """Check if the agent is ready to process requests"""
        return self.client is not None
    
    def get_response(self, user_message, image_data=None):
        """
        Get response from the AI agent
        
        Args:
            user_message (str): User's text message
            image_data (dict): Optional image data with 'url' or 'base64' key
            
        Returns:
            str: Agent's response
        """
        if not self.is_ready():
            return """❌ AI Agent not configured. 

Please check your .env file configuration:
- AZURE_OPENAI_ENDPOINT
- AZURE_OPENAI_KEY

Restart the application after updating the configuration."""

        try:
            # Build message content
            content = []
            
            # Add image if provided (for future image support)
            if image_data:
                if 'url' in image_data:
                    content.append({
                        "type": "image_url",
                        "image_url": {"url": image_data["url"]}
                    })
                elif 'base64' in image_data:
                    content.append({
                        "type": "image_url",
                        "image_url": {"url": f"data:{image_data.get('media_type', 'image/png')};base64,{image_data['base64']}"}
                    })
            
            # Add text message
            content.append({
                "type": "text",
                "text": user_message
            })
            
            # Add to conversation history
            self.conversation_history.append({
                "role": "user",
                "content": content if len(content) > 1 else user_message
            })
            
            # Prepare messages for API call
            messages = [
                {"role": "system", "content": self.system_prompt}
            ] + self.conversation_history
            
            # Call Azure OpenAI API
            response = self.client.chat.completions.create(
                model=Config.AZURE_OPENAI_DEPLOYMENT,
                messages=messages,
                max_tokens=Config.MAX_TOKENS,
                temperature=Config.TEMPERATURE
            )
            
            # Extract response text
            assistant_message = response.choices[0].message.content
            
            # Add to conversation history
            self.conversation_history.append({
                "role": "assistant",
                "content": assistant_message
            })
            
            return assistant_message
            
        except Exception as e:
            return f"❌ Error: {str(e)}\n\nPlease check your configuration and internet connection."
    
    def reset_conversation(self):
        """Reset the conversation history"""
        self.conversation_history = []
        return "Conversation history cleared. Starting fresh!"
    
    def get_conversation_length(self):
        """Get the number of messages in conversation history"""
        return len(self.conversation_history)
