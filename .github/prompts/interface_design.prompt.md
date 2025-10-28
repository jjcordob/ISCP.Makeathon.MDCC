---
mode: Vibe_code_assistant
---

# MDCC - Interface Design Reference

## Application Overview
**MDCC (Multimedia Document Code Converter)** - An AI-powered application that converts pictures and documents into markdown files for VSCode Copilot context or complete SystemVerilog verification environments (UVM-based) and RTL designs with multiple file outputs.

## Interface Layout

```
╔════════════════════════════════════════════════════════════════════════════════════════════════╗
║                           MDCC - Multimedia Document Code Converter                            ║
╠════════════════════════════════════════════════════════════════════════════════════════════════╣
║                                                                                                ║
║  ┌─────────────────────────────────────────┐    ┌──────────────────────────────────────────┐  ║
║  │       INPUT SOURCE                      │    │        OUTPUT OPTIONS                    │  ║
║  ├─────────────────────────────────────────┤    ├──────────────────────────────────────────┤  ║
║  │   📷 [Upload Picture]                  │    │  ⚙️  Convert to:                        │  ║
║  │      - Block Diagram                    │    │     ○ Markdown (.md)                     │  ║
║  │      - Circuit Diagram                  │    │       └─ VSCode Copilot Context          │  ║
║  │      - Handwritten Notes                │    │     ● RTL Design (.sv)                   │  ║
║  │                                         │    │       └─ Module + Interfaces             │  ║
║  │   📄 [Upload Document]                 │    │     ○ UVM Verification Env               │  ║
║  │      - RTL Functionality Desc.          │    │       └─ Multiple Files:                 │  ║
║  │      - Verification Requirements        │    │          • Test                          │  ║
║  │      - Design Specifications            │    │          • Scoreboard                    │  ║
║  └─────────────────────────────────────────┘    │          • Sequences                     │  ║
║                                                  │          • Agent/Driver/Monitor          │  ║
║                                                  │          • Coverage/Assertions           │  ║
║                                                  └──────────────────────────────────────────┘  ║
║                                                                                                ║
║  ┌──────────────────────────────────────────────────────────────────────────────────────────┐  ║
║  │  💬 EXTRA SPECIFICATIONS (Chat with AI Agent)                                           │  ║
║  ├──────────────────────────────────────────────────────────────────────────────────────────┤  ║
║  │  Add more details, constraints, or specific requirements...                             │  ║
║  │  ┌────────────────────────────────────────────────────────────────────────────────────┐ │  ║
║  │  │ User: "Add a reset synchronizer to the design"                                     │ │  ║
║  │  │ 🤖 Agent: "I'll add a 2-stage reset synchronizer. Any specific clock domain?"      │ │  ║
║  │  │ User: "Use async reset, sync release pattern"                                      │ │  ║
║  │  │ 🤖 Agent: "Understood. I'll implement async reset with synchronous release."       │ │  ║
║  │  │                                                                                     │ │  ║
║  │  │ [Type your specifications here...]                                          [Send] │ │  ║
║  │  └────────────────────────────────────────────────────────────────────────────────────┘ │  ║
║  └──────────────────────────────────────────────────────────────────────────────────────────┘  ║
║                                                                                                ║
║  ┌──────────────────────────────────────────────────────────────────────────────────────────┐  ║
║  │                           PREVIEW AREA                                                   │  ║
║  │  ┌────────────────────────────┬────────────────────────────────────────────────────────┐ │  ║
║  │  │  📤 INPUT PREVIEW         │  📥 OUTPUT PREVIEW                                      │ │  ║
║  │  ├────────────────────────────┼────────────────────────────────────────────────────────┤ │  ║
║  │  │                            │  📂 Generated Files:                                   │ │  ║
║  │  │  [Image/Document shown]    │  ├─ counter.sv                                        │ │  ║
║  │  │                            │  ├─ counter_if.sv                                     │ │  ║
║  │  │  ┌──────────────────────┐  │  ├─ counter_test.sv                                  │ │  ║
║  │  │  │   📄 Block Diagram   │  │  ├─ counter_scoreboard.sv                            │ │  ║
║  │  │  │   or                 │  │  ├─ counter_coverage.sv                              │ │  ║
║  │  │  │   Verification Spec  │  │  └─ counter_assertions.sv                            │ │  ║
║  │  │  │                      │  │                                                        │ │  ║
║  │  │  │   [Image Preview]    │  │  🔍 Currently Viewing: counter.sv                     │ │  ║
║  │  │  │                      │  │  ```systemverilog                                      │ │  ║
║  │  │  └──────────────────────┘  │  module counter (                                     │ │  ║
║  │  │                            │    input wire clk,                                    │ │  ║
║  │  │  Status: ✓ Loaded         │    input wire reset,                                  │ │  ║
║  │  │                            │    output reg [7:0] count                             │ │  ║
║  │  │                            │  );                                                   │ │  ║
║  │  │                            │    always @(posedge clk) begin                        │ │  ║
║  │  │                            │      if (reset) count <= 8'h0;                        │ │  ║
║  │  │                            │      else count <= count + 1;                         │ │  ║
║  │  │                            │    end                                                │ │  ║
║  │  │                            │  endmodule                                            │ │  ║
║  │  │                            │  ```                                                  │ │  ║
║  │  │                            │  Status: ⚡ Generating 6 files...                     │ │  ║
║  │  └────────────────────────────┴────────────────────────────────────────────────────────┘ │  ║
║  └──────────────────────────────────────────────────────────────────────────────────────────┘  ║
║                                                                                                ║
║  ┌──────────────────────────────────────────────────────────────────────────────────────────┐  ║
║  │  ACTIONS                                                                                 │  ║
║  │  [ 🔄 Process ] [ 💾 Save All Files ] [ 💾 Save Selected ] [ 📋 Copy ] [ 🗑️ Clear ]  │  ║
║  └──────────────────────────────────────────────────────────────────────────────────────────┘  ║
║                                                                                                ║
║  ┌──────────────────────────────────────────────────────────────────────────────────────────┐  ║
║  │  📜 PROCESSING LOG                                                                       │  ║
║  │  ✓ Image uploaded successfully (2.3 MB)                                                 │  ║
║  │  ⚡ AI analysis in progress...                                                           │  ║
║  │  ✓ Detected block diagram with counter module                                           │  ║
║  │  ✓ Generating RTL design files...                                                       │  ║
║  │  ✓ Created counter.sv (RTL module)                                                      │  ║
║  │  ✓ Created counter_if.sv (Interface)                                                    │  ║
║  │  ⚡ Generating UVM verification environment...                                           │  ║
║  │  ✓ Created counter_test.sv (UVM Test)                                                   │  ║
║  │  ✓ Created counter_scoreboard.sv (Scoreboard)                                           │  ║
║  │  ✓ Created counter_coverage.sv (Functional Coverage & Covergroups)                      │  ║
║  │  ✓ Created counter_assertions.sv (SVA Assertions)                                       │  ║
║  │  ✓ All 6 files generated successfully!                                                  │  ║
║  └──────────────────────────────────────────────────────────────────────────────────────────┘  ║
║                                                                                                ║
╚════════════════════════════════════════════════════════════════════════════════════════════════╝
```

## Core Features

### 1. Input Sources
- **📷 Upload Picture**: 
  - Block diagrams (generates complete RTL + interfaces)
  - Circuit diagrams (generates RTL modules)
  - Handwritten notes (extracts specifications)
  - Supported formats: PNG, JPG, JPEG, BMP
  
- **📄 Upload Document**: 
  - RTL functionality descriptions (generates RTL design)
  - Verification requirements (generates UVM verification environment)
  - Design specifications (generates markdown context for VSCode Copilot)
  - Supported formats: PDF, DOCX, TXT

### 2. Output Options
- **Markdown (.md)**: 
  - VSCode Copilot context files
  - Design documentation
  - Specification summaries
  
- **RTL Design (.sv)**: 
  - Main module file(s)
  - Interface definitions
  - Package files (if needed)
  
- **UVM Verification Environment**: 
  - **Test files**: UVM test classes and sequences
  - **Scoreboard**: Data checking and comparison logic
  - **Sequences**: Stimulus generation (sequence items and sequences)
  - **Agent Components**: Driver, Monitor, Sequencer
  - **Coverage**: Functional coverage and covergroups
  - **Assertions**: SystemVerilog Assertions (SVA) for property checking

### 3. Split-Panel Preview
- **Left Panel - Input Preview**: 
  - Display uploaded image/document
  - Image manipulation controls (zoom, rotate)
  
- **Right Panel - Output Preview**:
  - **File tree view** showing all generated files
  - **File selector** to switch between generated files
  - Live markdown rendering
  - Syntax-highlighted SystemVerilog code preview
  - UVM component visualization
  - Processing status indicators

### 4. Extra Specifications Chat
- **Interactive AI Agent**: Real-time conversation with the AI processing agent
- **Refinement**: Add specific requirements after initial file upload
- **Clarifications**: Ask questions about the generated code
- **Modifications**: Request changes to generated files (e.g., "Add parameter for bus width")
- **Constraints**: Specify design constraints, timing requirements, or verification coverage goals
- **Examples**:
  - "Make the counter parameterizable with configurable width"
  - "Add overflow detection and flag"
  - "Include assertion for checking counter never exceeds max value"
  - "Generate directed tests for edge cases"
  - "Add covergroup for all counter transitions"

### 5. Action Buttons
- **🔄 Process**: Start AI conversion and file generation
- **💾 Save All Files**: Download all generated files as a ZIP
- **💾 Save Selected**: Download currently viewed file
- **📋 Copy**: Copy current file content to clipboard
- **🗑️ Clear**: Reset interface

### 6. Processing Log
- Real-time feedback on AI processing steps
- Error messages and warnings
- Success confirmations
- Processing time tracking

## Technical Components

### Frontend
- Modern, responsive UI framework (React/Vue/Svelte)
- Split-panel layout with resizable dividers
- Real-time preview rendering
- Drag-and-drop file upload
- File type validation
- **Chat interface** for AI agent interaction
- WebSocket for real-time agent responses

### Backend
- AI integration (OpenAI GPT-4 Vision API, Claude Vision, etc.)
- **Conversational AI agent** for requirement refinement
- Image processing pipeline
- OCR capabilities
- **SystemVerilog RTL code generation**
- **UVM testbench architecture generation**
- **Multi-file project structure generation**
- **Iterative code refinement** based on user chat input
- File format conversion
- Session management
- ZIP file creation for batch downloads
- Chat history and context management

### Key Technologies
- **AI/ML**: GPT-4 Vision, OCR engines, text recognition, diagram analysis
- **File Processing**: Image manipulation, PDF parsing, document conversion
- **Real-time Features**: WebSocket for live updates, streaming responses
- **Storage**: Temporary file storage, session caching, multi-file management
- **Hardware Description**: 
  - SystemVerilog RTL synthesis
  - UVM methodology and best practices
  - SVA (SystemVerilog Assertions) generation
  - Functional coverage and covergroup creation
  - Interface and package generation

## User Flow

1. **Upload**: User uploads a picture (block/circuit diagram) or document (specifications/requirements)
2. **Preview**: System displays input in left panel
3. **Select Format**: User chooses between:
   - Markdown (for VSCode Copilot context)
   - RTL Design (generates module + interfaces)
   - UVM Verification Environment (generates complete testbench with multiple files)
4. **Refine (Optional)**: User interacts with AI agent via chat to:
   - Add specific constraints or parameters
   - Request modifications to the design approach
   - Clarify requirements or ask questions
   - Specify additional features (e.g., error handling, edge case coverage)
5. **Process**: AI analyzes input and chat context, then generates appropriate files
6. **Review**: Right panel shows file tree and allows navigation between generated files
7. **Iterate (Optional)**: User can continue chatting with agent to refine generated code
8. **Export**: User can:
   - Download all files as ZIP
   - Download individual files
   - Copy file contents to clipboard

## Input-to-Output Mapping

### Picture Input Examples:
- **Block Diagram** → RTL modules + Interfaces + (optionally) UVM Verification Environment
- **Circuit Diagram** → RTL implementation
- **Handwritten Specs** → Markdown context for Copilot

### Document Input Examples:
- **RTL Functionality Description** → Complete RTL design (module + interfaces)
- **Verification Requirements** → UVM Verification Environment:
  - Test scenarios and sequences
  - Scoreboard with checking logic
  - Coverage model (covergroups)
  - Assertions (SVA)
  - Agent components (driver, monitor, sequencer)
- **Design Specifications** → Markdown documentation for VSCode Copilot context

## Accessibility Features
- Keyboard navigation support
- Screen reader compatibility
- High contrast mode
- Adjustable font sizes
- Clear status indicators

## Future Enhancements
- Batch processing multiple files
- History/Recent conversions
- **Save and load chat sessions** for iterative refinement across sessions
- Custom AI prompts for SystemVerilog generation
- **UVM methodology templates** (different verification architectures)
- **Testbench generation** with configurable UVM base test
- Support for additional hardware description languages (VHDL, Verilog)
- **Advanced diagram recognition**:
  - FSM (Finite State Machine) diagrams → RTL + verification
  - Timing diagrams → Sequence generation
  - Protocol diagrams → Interface + monitor generation
- **Smart file organization**: Auto-create proper directory structure
- **Constraint generation**: SystemVerilog constraint blocks for randomization
- **Integration with EDA tools**: Export configurations for simulators
- **Code quality metrics**: Linting and best practice suggestions for generated code
- **Voice input** for chat specifications
- **Multi-turn refinement tracking**: Show version history of generated files
