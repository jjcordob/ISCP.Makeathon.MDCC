---
applyTo: '**'
---

# DVA (Design Verification Alchemist) Instructions
Inspired by Full Metal Alchemist, DVA transforms ("transmutes") hand-written notes, diagrams, and specifications into production-ready SystemVerilog code.

This application leverages AI vision capabilities to process multimedia inputs—from camera captures to document uploads—and generate hardware RTL or verification environments.

**Core Alchemy:** Hand-drawn block diagrams, state machines, flow diagrams, or notes on paper sheets → SystemVerilog RTL or verification code

## RTL Transmutation (Generation)
DVA allows users to **snap photos of hand-written notes on paper sheets** or upload digital documents. The AI vision processes these images—extracting block diagrams, state machines, timing diagrams, and design notes—then transmutes them into synthesizable SystemVerilog RTL code.

**Input Examples:**
- Napkin sketches of state diagrams
- Whiteboard photos of block diagrams
- Hand-drawn timing diagrams on paper
- Tablet notes with flow diagrams
- PDF specification documents

The generated RTL is optimized for performance, follows IEEE 1800 standards, and can be output as single or multiple files based on design complexity.

## Verification Environment Transmutation
DVA transmutes verification requirements from any visual source into complete SystemVerilog verification code: assertions (SVA), covergroups, checkers, or full UVM environments.

**Input Examples:**
- Hand-written test scenarios on paper
- Photos of coverage matrices
- Sketches of assertion requirements
- Notes about protocol checkers

**Output Options (configurable):**
- SystemVerilog Assertions (SVA) only
- Functional coverage (covergroups) only
- Protocol checkers
- Complete UVM testbench environment

All generated code includes requirement traceability, error handling, and follows UVM/SVA best practices.

## Alchemist Agent
The DVA agent can accept additional context to guide the transmutation process. If the input cannot be converted into RTL or verification code (e.g., unrelated content), the agent will inform the user and request valid design/verification material.

**Alchemy Law:** Equivalent exchange—quality output requires quality input. Clear diagrams and specifications yield better code.