# MDCC Application - Issues and Resolutions Report

## Project Overview
**MDCC (Multimedia Design Code Converter)** - An AI-powered application for converting hand-drawn diagrams and notes into RTL code and verification environments.

**Date:** October 27, 2025  
**Technology Stack:** Python, Tkinter, Azure OpenAI, httpx

---

## Issues Encountered and Resolutions

### 1. Missing Dependencies
**Issue:** Application failed to start due to missing Python packages.
```
ModuleNotFoundError: No module named 'openai'
```

**Root Cause:** Required packages were not installed in the Python environment.

**Resolution:**
- Added dependencies to `requirements.txt`:
  - `openai>=1.0.0` - Azure OpenAI SDK
  - `python-dotenv>=1.0.0` - Environment variable management
  - `httpx>=0.24.0` - HTTP client for proxy configuration
- Installed packages using: `pip install -r requirements.txt`

**Files Modified:**
- `requirements.txt`

---

### 2. HTTP Client Proxy Configuration Error
**Issue:** Incorrect syntax when configuring httpx client with proxy settings.
```
TypeError: Client.__init__() got an unexpected keyword argument 'proxies'
```

**Root Cause:** Used incorrect parameter name `proxies` (plural) instead of `proxy` (singular) in httpx.Client initialization.

**Resolution:**
Changed from:
```python
http_client = httpx.Client(
    proxies={
        "http://": Config.HTTP_PROXY,
        "https://": Config.HTTP_PROXY
    }
)
```

To:
```python
http_client = httpx.Client(
    proxy=Config.HTTP_PROXY,
    verify=False
)
```

**Files Modified:**
- `agent.py`

---

### 3. Intel Proxy Network Access Issue
**Issue:** Connection blocked by Intel DMZ proxy when trying to access internal GenAI service.
```
Access Denied - The page you have requested has been blocked by a proxy policy restriction.
```

**Root Cause:** 
- `genai-proxy.intel.com` is an **internal** Intel service
- Was attempting to access it through **DMZ proxy** (`proxy-dmz.intel.com:912`)
- DMZ proxy only allows access to external websites, not internal Intel resources

**Resolution:**
- Changed from DMZ proxy to **Intel Chain proxy** for internal network access
- Updated proxy configuration:
  - From: `http://proxy-dmz.intel.com:912`
  - To: `http://proxy-chain.intel.com:911`
- Hard-coded the correct proxy in the AzureOpenAI client initialization

**Files Modified:**
- `.env` (proxy configuration)
- `agent.py` (http_client initialization)

**Final Working Configuration:**
```python
self.client = AzureOpenAI(
    api_key=Config.AZURE_OPENAI_KEY,
    api_version=Config.AZURE_OPENAI_API_VERSION,
    azure_endpoint=Config.AZURE_OPENAI_ENDPOINT,
    http_client=httpx.Client(
        verify=False,
        proxy="http://proxy-chain.intel.com:911"
    )
)
```

---

### 4. SSL Verification Issues
**Issue:** Corporate proxy and internal certificates causing SSL verification failures.

**Resolution:**
- Disabled SSL verification in httpx.Client with `verify=False`
- This is acceptable for internal corporate environments with self-signed certificates

**Security Note:** SSL verification is disabled only for internal Intel network access. For production external APIs, SSL verification should be enabled.

---

## Final Architecture

### File Structure
```
MDCC/
├── app.py              # Main Tkinter GUI application
├── agent.py            # AI agent with Azure OpenAI integration
├── config.py           # Configuration management from .env
├── requirements.txt    # Python dependencies
└── .env               # Environment variables (API keys, proxy settings)
```

### Environment Variables (.env)
```env
AZURE_OPENAI_ENDPOINT=https://genai-proxy.intel.com/api
AZURE_OPENAI_KEY=genai__[key]
AZURE_OPENAI_API_VERSION=2025-01-01-preview
AZURE_OPENAI_MODEL_NAME=gpt-4.1
AZURE_OPENAI_DEPLOYMENT=gpt-4.1
HTTP_PROXY=http://proxy-chain.intel.com:911
AZURE_OPENAI_MAX_TOKENS=16384
AZURE_OPENAI_TEMPERATURE=0.7
```

### Key Components

1. **app.py** - GUI Interface
   - Tkinter-based chat interface
   - Dark theme (VS Code style)
   - Real-time AI interaction
   - Status monitoring

2. **agent.py** - AI Integration
   - Azure OpenAI client with proxy support
   - Conversation history management
   - Specialized system prompt for RTL/verification
   - Error handling and connection validation

3. **config.py** - Configuration
   - Environment variable loading
   - API key validation
   - Centralized settings management

---

## Lessons Learned

1. **Proxy Configuration:** Internal vs. external proxy servers serve different purposes:
   - DMZ proxy: External internet access only
   - Chain proxy: Internal + external access

2. **httpx Library:** Parameter names matter - `proxy` (singular) not `proxies` (plural)

3. **SSL in Corporate Networks:** Self-signed certificates require `verify=False` for internal services

4. **Error Messages:** HTML responses instead of JSON indicate proxy interception/blocking

---

## Current Status

✅ **Application is fully functional**
- AI agent successfully connects to Azure OpenAI
- Proxy configuration working correctly
- Chat interface operational
- Ready for RTL/verification code generation tasks

---

## Next Steps (Future Enhancements)

1. Add image upload functionality for diagram processing
2. Implement camera capture for real-time diagram conversion
3. Add file export for generated RTL code
4. Create syntax highlighting for code responses
5. Add conversation history export
6. Implement reset/clear conversation button

---

## Contact & Support

For issues related to:
- **Proxy access:** Open IT support ticket via Intel IT portal
- **GenAI API:** Contact GenAI platform team
- **Application bugs:** Check repository issues or contact development team
