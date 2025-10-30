"""
Configuration management for MDCC application
Handles API keys and application settings using Azure OpenAI configuration
"""

import os
from dotenv import load_dotenv

# Load environment variables from .env file
load_dotenv()


class Config:
    """Application configuration class"""
    
    # Azure OpenAI Configuration
    AZURE_OPENAI_ENDPOINT = os.getenv("AZURE_OPENAI_ENDPOINT", "")
    AZURE_OPENAI_KEY = os.getenv("AZURE_OPENAI_KEY", "")
    AZURE_OPENAI_API_VERSION = os.getenv("AZURE_OPENAI_API_VERSION", "2025-01-01-preview")
    AZURE_OPENAI_MODEL_NAME = os.getenv("AZURE_OPENAI_MODEL_NAME", "gpt-4.1")
    AZURE_OPENAI_DEPLOYMENT = os.getenv("AZURE_OPENAI_DEPLOYMENT", "gpt-4.1")
    
    # Proxy Configuration
    HTTP_PROXY = os.getenv("HTTP_PROXY", "")
    
    # Model settings
    MAX_TOKENS = int(os.getenv("AZURE_OPENAI_MAX_TOKENS", "16384"))
    TEMPERATURE = float(os.getenv("AZURE_OPENAI_TEMPERATURE", "0.7"))
    
    # Application settings
    APP_NAME = "MDCC - Multimedia Design Code Converter"
    VERSION = "0.1.0"
    
    @classmethod
    def validate(cls):
        """Validate configuration"""
        if not cls.AZURE_OPENAI_ENDPOINT:
            return False, "AZURE_OPENAI_ENDPOINT not found in environment variables"
        if not cls.AZURE_OPENAI_KEY:
            return False, "AZURE_OPENAI_KEY not found in environment variables"
        return True, "Configuration valid"
    
    @classmethod
    def get_api_key_status(cls):
        """Check if API key is configured"""
        if cls.AZURE_OPENAI_KEY and cls.AZURE_OPENAI_ENDPOINT:
            return True
        return False
