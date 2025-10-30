# ⚗️ DVA - Design Verification Alchemist

![Python Version](https://img.shields.io/badge/python-3.14.0-blue)
![License](https://img.shields.io/badge/license-MIT-green)
![Status](https://img.shields.io/badge/status-active-success)

## 📋 Overview

**DVA (Design Verification Alchemist)** - Inspired by Full Metal Alchemist, transmutes hand-written notes, diagrams, and specifications into production-ready SystemVerilog code.

🎯 **The Ultimate Transmutation:** Snap a photo of hand-drawn notes on paper → Complete SystemVerilog RTL or verification environment

The application leverages AI vision to analyze:
- **Paper notes** - Hand-written specifications on sheets
- **Whiteboard photos** - Block diagrams, state machines
- **Napkin sketches** - Quick design ideas
- **Tablet drawings** - Digital handwritten notes
- **PDF documents** - Formal specifications
- **Timing diagrams** - Protocol descriptions

And transmutes them into:
- **SystemVerilog RTL** - Synthesizable hardware modules
- **SVA Assertions** - Formal property checkers
- **Covergroups** - Functional coverage code
- **UVM Environments** - Complete testbench infrastructure
- **Markdown Docs** - Traceable requirement documentation

## ✨ Features

### 🎯 Core Alchemy Powers
- **� Paper-to-RTL** - Snap photos of hand-drawn diagrams → Working hardware code
- **⚗️ Vision-First Processing** - AI filters pages (scores 0-10), keeps only specs
- **✅ Expert Review** - SystemVerilog expert validates code on 8 quality criteria
- **🎨 Multimedia Input** - Camera capture, document upload, real-time processing
- **💬 AI Chat Assistant** - Separate chat window for design consultations
- **👁️ Results Preview** - Tabbed interface for viewing generated files
- **💾 Flexible Export** - Save individual files or entire file sets

### 🎨 User Interface
- **Clean, Modern Design** - Dark-themed professional interface
- **Input Preview** - Live preview of captured images
- **Processing Log** - Real-time status updates with color-coded messages
- **Tabbed Results** - Organized view of multiple generated files
- **Keyboard Shortcuts** - Enhanced productivity with keyboard support

## � Project Structure

```
MDCC/
├── app.py                          # Main application entry point
├── requirements.txt                # Python dependencies
├── .env                           # Environment configuration (not in repo)
├── README.md                      # This file
│
├── src/                           # Source code modules
│   ├── __init__.py
│   ├── agent.py                   # Main AI agent interface
│   ├── ai_validator.py            # AI-powered section validator
│   ├── config.py                  # Configuration management
│   ├── document_processor.py      # Document processing and NLP
│   ├── verification_agents.py     # Specialized verification agents
│   └── vision_document_processor.py # Vision-based document analysis
│
├── docs/                          # Documentation
│   ├── README.md                  # Documentation index
│   ├── VISION_PROCESSING.md       # Vision pipeline details
│   ├── EXPERT_REVIEW.md           # Expert review feature
│   ├── VERSION_TRACKER.md         # Version history
│   └── ISSUES_AND_RESOLUTIONS.md  # Known issues and fixes
│
├── icons/                         # Application icons and images
│   ├── icon2.png                  # Application icon
│   ├── name1.png                  # Logo/branding
│   ├── welcome.png                # Splash screen
│   └── chat.png                   # Chat window icon
│
└── .github/                       # GitHub specific files
    ├── instructions/              # AI coding instructions
    ├── prompts/                   # AI prompt templates
    └── chatmodes/                 # Chat mode configurations
```

## �🚀 Getting Started

### Prerequisites

- Python 3.14.0 or higher
- Webcam (optional, for camera capture feature)
- Azure OpenAI API credentials

### Installation

1. **Clone the repository**
   ```powershell
   git clone https://github.com/jjcordob/ISCP.Makeathon.MDCC.git
   cd MDCC
   ```

2. **Create and activate virtual environment**
   ```powershell
   python -m venv venv
   .\venv\Scripts\Activate.ps1
   ```

3. **Install dependencies**
   ```powershell
   pip install -r requirements.txt
   ```

4. **Configure environment variables**
   
   Create a `.env` file in the project root:
   ```env
   AZURE_OPENAI_API_KEY=your_api_key_here
   AZURE_OPENAI_ENDPOINT=your_endpoint_here
   AZURE_OPENAI_API_VERSION=2024-02-15-preview
   AZURE_OPENAI_MODEL_NAME=your_model_name
   ```

### Running the Application

**With Virtual Environment:**
```powershell
.\venv\Scripts\python.exe app.py
```

**Or activate venv first:**
```powershell
.\venv\Scripts\Activate.ps1
python app.py
```

## 📖 How to Use

### Basic Workflow

1. **Select Output Mode**
   - Choose between RTL Design, Markdown Documentation, or UVM Verification Environment

2. **Capture/Upload Input**
   - **Camera**: Click "📷 Upload Picture / Camera" to capture a diagram
   - **Document**: Click "📄 Upload Document" to load a specification file

3. **Process**
   - Click "🔄 Process" to send your input to the AI agent
   - Monitor progress in the Processing Log

4. **View Results**
   - Click "👁️ View Results" to see generated code in a tabbed window
   - Each file appears in its own tab for easy navigation

5. **Save or Copy**
   - **💾 Save All Files**: Choose a directory to save all generated files
   - **📋 Copy**: Copy all generated code to clipboard

### Advanced Features

#### AI Chat Assistant
- Click "💬 Chat with AI Agent" in the header
- Ask questions about RTL design, UVM strategies, or SystemVerilog
- Get expert advice without processing images

#### Multiple Output Types

**RTL Mode** - Generates:
- Module definitions with proper interfaces
- Always blocks for combinational/sequential logic
- Parameter declarations
- Complete, synthesizable SystemVerilog code

**UVM Mode** - Generates complete verification environment:
- `tb_top.sv` - Testbench top module
- `test.sv` - Test sequences
- `env.sv` - UVM environment
- `scoreboard.sv` - Checker component
- `agent.sv` - Agent configuration
- `driver.sv` - Driver component
- `monitor.sv` - Monitor component
- `sequences.sv` - Sequence library
- `coverage.sv` - Coverage definitions

**Markdown Mode** - Generates:
- Structured design documentation
- Section headers and formatting
- Ready for GitHub or VSCode Copilot context

## 🏗️ Project Structure

```
MDCC/
│
├── app.py                      # Main application with GUI
├── agent.py                    # AI agent integration
├── config.py                   # Configuration management
├── requirements.txt            # Python dependencies
├── .env                        # Environment variables (not in repo)
│
├── .github/
│   └── instructions/
│       └── MDCC_instructions.instructions.md
│
├── docs/
│   ├── README.md              # This file
│   ├── VERSION_TRACKER.md     # Version history
│   └── ISSUES_AND_RESOLUTIONS.md  # Problem solving log
│
└── venv/                      # Virtual environment (not in repo)
```

## 🎯 Use Cases

### Hardware Design
- Convert hand-drawn block diagrams into RTL modules
- Transform state machines into SystemVerilog
- Generate interfaces from connectivity diagrams

### Verification
- Create UVM testbenches from test plans
- Generate coverage models from specification notes
- Build scoreboards from checking requirements

### Documentation
- Convert whiteboard sessions into markdown
- Document design decisions from meeting notes
- Create specification documents from diagrams

## ⚙️ Configuration

### Environment Variables

| Variable | Description | Required |
|----------|-------------|----------|
| `AZURE_OPENAI_API_KEY` | Your Azure OpenAI API key | Yes |
| `AZURE_OPENAI_ENDPOINT` | Azure OpenAI endpoint URL | Yes |
| `AZURE_OPENAI_API_VERSION` | API version (e.g., 2024-02-15-preview) | Yes |
| `AZURE_OPENAI_MODEL_NAME` | Model deployment name | Yes |

### UI Customization

Edit `app.py` to customize colors:
```python
self.bg_color = "#1e1e1e"      # Background
self.fg_color = "#ffffff"       # Foreground text
self.panel_bg = "#2d2d30"       # Panel background
self.button_bg = "#007acc"      # Button color
```

## 🐛 Troubleshooting

### Camera Issues
- **Camera won't open**: Check if another application is using the camera
- **Black screen**: Ensure proper camera permissions in Windows settings
- **Poor quality**: Improve lighting and reduce glare on diagrams

### API Issues
- **Not configured error**: Verify `.env` file exists and has correct credentials
- **Timeout errors**: Check internet connection and Azure endpoint availability
- **Empty responses**: Ensure image is clear and diagrams are visible

### Generated Code Issues
- **No files extracted**: AI may have returned explanation text instead of code
- **Incorrect modules**: Try improving diagram clarity or add text annotations
- **Missing files**: Some complex designs may need manual file splitting

## 🤝 Contributing

Contributions are welcome! Please:
1. Fork the repository
2. Create a feature branch
3. Commit your changes
4. Push to the branch
5. Open a Pull Request

## 📝 License

This project is licensed under the MIT License - see the LICENSE file for details.

## 👥 Authors

- **jjcordob** - *Initial work and development*

## 🙏 Acknowledgments

- Azure OpenAI for AI capabilities
- OpenCV for camera integration
- Tkinter for GUI framework
- The SystemVerilog and UVM communities

## 📧 Support

For issues, questions, or suggestions:
- Open an issue on GitHub
- Contact: [Your contact information]

## 🔄 Version

Current Version: **1.0.0**

See [docs/VERSION_TRACKER.md](docs/VERSION_TRACKER.md) for detailed version history.

## 📚 Documentation

For detailed documentation, see the [docs](docs/) directory:
- [Vision Processing](docs/VISION_PROCESSING.md) - AI vision pipeline details
- [Expert Review](docs/EXPERT_REVIEW.md) - SV/UVM expert review feature
- [Version History](docs/VERSION_TRACKER.md) - Changelog and updates
- [Issues & Resolutions](docs/ISSUES_AND_RESOLUTIONS.md) - Troubleshooting guide

---

**Made with ❤️ for the hardware design and verification community**
