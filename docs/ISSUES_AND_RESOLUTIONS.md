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

### 7. UI Layout Issues - Hidden Action Panels
**Issue:** Action buttons panel was not visible in the main window, appearing cut off below the visible area.

**Root Cause:** Multiple panels were set to `expand=True`, causing the chat and preview panels to consume all available vertical space, pushing the action panel out of view.

**Resolution:**
- Set `expand=False` on chat panel and preview area
- Reduced fixed heights:
  - Chat display: `height=2` lines
  - Preview area: `height=200` pixels
  - Processing log: `height=3` lines
- Ensured action panel and processing log were always visible within 900px window height

**Files Modified:**
- `app.py` (lines 250-470)

**Verification:**
- All six sections now fit within 1400x900 window
- Minimum window size set to 1200x800

---

### 8. AI Output Format Issues - Mixed Text and Code
**Issue:** AI responses included explanatory text mixed with code, making file extraction difficult and cluttering the output.

**Root Cause:** Generic prompts allowed AI to provide explanations and context along with code.

**Resolution:**
Implemented strict "code-only" prompts with explicit formatting requirements:
```python
"""Analyze this diagram and generate ONLY the SystemVerilog RTL code. 

CRITICAL INSTRUCTIONS:
- NO explanations, NO comments outside code, NO markdown text
- Return ONLY code wrapped in code blocks
- Format: ```systemverilog:filename.sv for each file
...
RETURN ONLY CODE IN THIS FORMAT - NO OTHER TEXT."""
```

**Impact:**
- Clean code extraction without manual filtering
- Consistent file generation across all modes
- Improved parsing reliability

**Files Modified:**
- `app.py` (process_input method, lines 800-875)

---

### 9. Multi-File Extraction Challenges
**Issue:** Generated code was not being properly extracted into separate files when AI returned multiple modules.

**Root Cause:** Initial regex pattern only looked for explicit filename markers (`systemverilog:filename.sv`), missing standalone code blocks.

**Resolution:**
Implemented three-tier extraction strategy:
1. **Primary**: Explicit filename parsing (````systemverilog:filename.sv`)
2. **Fallback 1**: Module name detection from `module module_name` declarations
3. **Fallback 2**: Generic code block extraction with auto-naming

```python
def extract_files_from_response(self, response):
    # Strategy 1: Explicit filenames
    pattern = r'```(?:systemverilog|verilog|sv|markdown):([^\n]+)\n(.*?)```'
    matches = re.findall(pattern, response, re.DOTALL)
    
    if not matches:
        # Strategy 2: Module detection
        module_pattern = r'module\s+(\w+)'
        ...
    
    if not matches:
        # Strategy 3: Generic blocks
        generic_pattern = r'```(?:systemverilog|verilog|sv)?\n(.*?)```'
        ...
```

**Files Modified:**
- `app.py` (extract_files_from_response method, lines 740-790)

---

### 10. Output Display Limitations - Small Preview Area
**Issue:** Output preview text area was too small (200px height) to effectively view generated code, requiring excessive scrolling.

**Root Cause:** Limited screen real estate allocated to preview section in initial design.

**Resolution:**
Created dedicated results window:
- Separate 1000x700 Toplevel window
- Tabbed interface (ttk.Notebook) for multiple files
- Each file in its own tab for easy navigation
- Full-size code display with syntax-friendly Consolas font
- Copy and Save buttons at bottom

**Benefits:**
- Large, dedicated viewing area
- Clear file organization with tabs
- Non-modal window (can keep open while working)
- Better code readability

**Files Modified:**
- `app.py` (show_results_window method, lines 1000-1135)

---

### 11. Button Color Scheme Inconsistency
**Issue:** View Results button used default blue color (#007acc) which clashed with the dark theme and didn't match the green Process button.

**Root Cause:** Inconsistent color selection for button states.

**Resolution:**
Redesigned button states with cohesive color scheme:
- **Enabled state**: `bg=#2d7a3e` (green, matching Process button)
- **Disabled state**: `bg=#2d2d30` (gray, matching panel background)
- Applied to all result-related buttons for visual consistency

```python
self.view_results_btn.config(
    state=tk.NORMAL,
    bg="#2d7a3e",  # Green when enabled
    fg="#ffffff"
)
```

**Files Modified:**
- `app.py` (button configurations and state management)

---

### 12. Preview Area Underutilization
**Issue:** Preview Area panel contained only a single button (View Results) after moving input preview, wasting valuable screen space.

**Root Cause:** Feature evolution left the preview area with minimal content.

**Resolution:**
- Removed entire Preview Area panel (lines 313-402)
- Moved View Results button to Actions section alongside other action buttons
- Moved Input Preview to standalone panel above Actions
- Consolidated interface to 5 main sections instead of 6
- Reduced overall window clutter

**Benefits:**
- Cleaner, more focused interface
- All action buttons in one logical location
- Better use of vertical space
- Improved user workflow

**Files Modified:**
- `app.py` (layout restructure, lines 310-410)
- Removed `output_status` label references throughout

---

### 13. Chat Interface Integration Issues
**Issue:** Chat section in main window consumed too much space and wasn't frequently used during image processing workflow.

**Root Cause:** Chat and image processing are separate use cases that don't need to share screen space.

**Resolution:**
Separated chat functionality into dedicated window:
- Removed chat panel from main interface (60+ lines of code)
- Created "💬 Chat with AI Agent" button in header
- Opens separate 800x600 chat window on demand
- Full-featured chat with history, timestamps, and formatting
- Independent conversation context

**Benefits:**
- Main interface focuses on core workflow (input → process → view → save)
- Chat available when needed without cluttering main window
- Each window optimized for its specific purpose
- Can use both simultaneously (non-modal)

**Features of Separate Chat Window:**
- Welcome message with AI status
- Conversation history display
- 3-line input area with Send button
- Enter to send, Shift+Enter for newline
- Processing status indicators
- Close button

**Files Modified:**
- `app.py` (removed chat section, added `open_chat_window` method)
- Updated `process_input` to not depend on chat input

---

### 14. Python Environment Management
**Issue:** Running `python app.py` would sometimes use system Python instead of virtual environment, causing module import errors.

**Root Cause:** Virtual environment not activated or PATH issues in PowerShell.

**Resolution:**
Documented explicit commands for running with venv:

**Method 1 - Direct venv python:**
```powershell
C:/Users/jjcordob/Documents/Projects/MDCC/venv/Scripts/python.exe app.py
```

**Method 2 - Activate then run:**
```powershell
.\venv\Scripts\Activate.ps1
python app.py
```

**Tools Used:**
- `configure_python_environment` tool to detect and configure venv
- Ensured all development uses Python 3.14.0 from venv

**Files Modified:**
- Documentation (README.md)
- Development notes

---

### 15. State Management - Clear All Button
**Issue:** Clear All button didn't properly reset View Results button state, leaving it in an incorrect visual state.

**Root Cause:** Missing button state reset in `clear_all()` method.

**Resolution:**
Updated clear_all method to properly reset all UI elements:
```python
self.view_results_btn.config(
    state=tk.DISABLED,
    bg="#2d2d30",       # Gray disabled state
    fg="#cccccc",       # Muted text
    text="👁️ View Results"
)
```

Also resets:
- Image data (`captured_image`, `captured_image_tk`)
- Generated outputs (`generated_files`, `generated_output`)
- Input preview display
- Status labels
- Agent conversation history

**Files Modified:**
- `app.py` (clear_all method, lines 1135-1158)

---

## Development Best Practices Learned

### 1. Layout Management in Tkinter
- **Lesson**: Use `expand=False` and fixed heights for non-flexible panels
- **Impact**: Prevents layout issues in different window sizes
- **Application**: All panel configurations in main window

### 2. AI Prompt Engineering
- **Lesson**: Be extremely explicit about output format requirements
- **Impact**: Drastically improved code extraction success rate
- **Application**: All mode-specific prompts (RTL, UVM, Markdown)

### 3. Regex Pattern Fallbacks
- **Lesson**: Always implement multiple extraction strategies
- **Impact**: Robust file extraction even when AI varies format
- **Application**: Three-tier file extraction system

### 4. UI State Consistency
- **Lesson**: Every state change must update all related UI elements
- **Impact**: No orphaned states or visual inconsistencies
- **Application**: Button state management, clear operations

### 5. Separation of Concerns
- **Lesson**: Keep different workflows in separate UI contexts
- **Impact**: Cleaner, more focused user experience
- **Application**: Separate chat window vs. main processing interface

---

## Next Steps (Future Enhancements)

### Completed (v1.0.0)
- ✅ Image upload functionality (camera capture)
- ✅ File export for generated RTL code (multi-file save)
- ✅ Reset/clear conversation button

### Planned (v1.1.0+)
1. Implement PDF/DOCX document processing (currently UI only)
2. Add syntax highlighting for code in results window
3. Create template library for common RTL patterns
4. Implement conversation history export to file
5. Add batch processing for multiple diagrams
6. OCR enhancement for handwritten notes
7. Integration with VS Code (export workspace)
8. Local AI model support (offline mode)

---

## Contact & Support

For issues related to:
- **Proxy access:** Open IT support ticket via Intel IT portal
- **GenAI API:** Contact GenAI platform team
- **Application bugs:** Check repository issues or contact development team
