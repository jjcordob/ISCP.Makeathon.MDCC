---
applyTo: '**'
---

# MDCC Instructions
This is going to be an application with an interface that leverages AI capabilities to enhance user experience and functionality. The application will be designed to take multimedia files or access the camera as input to perform tasks, analyze data, and generate outputs.

Pictures of notes in the tablet, captures of documents, notes in a paper sheet, etc.. about block diagrams, state diagrams, descriptions flow diagrams written on hand or taken by spect will be converted into RTL or a verification environment

## RTL generation
The application will allow users to upload images or capture photos of their hand-drawn diagrams and notes. The AI will process these images to extract relevant information and convert them into RTL code. The generated RTL code will be optimized for performance and scalability, following established coding standards and conventions. Pictures will include notes, block diagrams, state diagrams, flow diagrams, and other relevant information.

RTL can be generated in different files or in a single file depending on the complexity of the design and user preferences.

## Verification environment generation
The application will also support the generation of verification environments based on the extracted information from the uploaded images. The AI will create testbenches, simulation scripts, and other necessary components to verify the functionality of the generated RTL code. The verification environment will be designed to ensure code quality and reliability, with robust error handling and input validation.

It can be pictures block diagrams, notes about checkers, assertions or covergroups, if the user wants a file just with covergroups, or assertions or checkers, it can be specified to the agent

## Agent
You can add extra information for the agent to process the multimedia input, if the input is not something that can be transformed into RTL or verification environment, the agent should inform the user about it and ask for new input.