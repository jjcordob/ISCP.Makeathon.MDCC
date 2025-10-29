"""
DVM - Design/Verif Maker
Main application file with GUI interface for AI agent interaction
"""

import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog
from datetime import datetime
from agent import DVMAgent
from config import Config
import cv2
import base64
from PIL import Image, ImageTk
import io
import re
import os


class DVMApp:
    """Main application class for DVM with chat interface"""
    
    def __init__(self, root):
        self.root = root
        self.root.title("DVM - Design/Verif Maker")
        self.root.geometry("1400x900")
        self.root.minsize(1200, 800)
        
        # Initialize AI agent
        self.agent = DVMAgent()
        
        # State variables
        self.output_mode = tk.StringVar(value="rtl")  # rtl, markdown, uvm
        self.captured_image = None
        self.captured_image_tk = None
        self.generated_files = {}
        self.generated_output = ""  # Store full output text
        self.current_file = None
        
        # Configure style
        self.setup_styles()
        
        # Create UI components
        self.create_widgets()
        
        # Check API status
        self.check_api_status()
        
    def setup_styles(self):
        """Configure application styles"""
        style = ttk.Style()
        style.theme_use('clam')
        
        # Configure colors
        self.bg_color = "#1e1e1e"
        self.fg_color = "#ffffff"
        self.input_bg = "#2d2d2d"
        self.button_bg = "#007acc"
        self.chat_bg = "#252526"
        self.panel_bg = "#2d2d30"
        self.border_color = "#3e3e42"
        
        # Configure root background
        self.root.configure(bg=self.bg_color)
        
    def create_widgets(self):
        """Create and layout all UI widgets"""
        # Main container
        main_frame = tk.Frame(self.root, bg=self.bg_color)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # ========== HEADER ==========
        header_frame = tk.Frame(main_frame, bg=self.bg_color)
        header_frame.pack(fill=tk.X, pady=(0, 10))
        
        title_label = tk.Label(
            header_frame,
            text="DVM - Design/Verif Maker",
            font=("Segoe UI", 18, "bold"),
            bg=self.bg_color,
            fg=self.fg_color
        )
        title_label.pack(side=tk.LEFT)
        
        # Chat with AI button
        chat_btn = tk.Button(
            header_frame,
            text="🧙‍♂️ DVM Alchemist",
            command=self.open_chat_window,
            bg="#007acc",
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=20,
            pady=8,
            cursor="hand2"
        )
        chat_btn.pack(side=tk.RIGHT)
        
        # ========== TOP SECTION: INPUT SOURCE + OUTPUT OPTIONS ==========
        top_section = tk.Frame(main_frame, bg=self.bg_color)
        top_section.pack(fill=tk.X, pady=(0, 10))
        
        # Left: Input Source Panel
        input_panel = tk.LabelFrame(
            top_section,
            text="  INPUT SOURCE  ",
            font=("Segoe UI", 11, "bold"),
            bg=self.panel_bg,
            fg=self.fg_color,
            relief=tk.GROOVE,
            bd=2
        )
        input_panel.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        
        # Picture upload section
        pic_frame = tk.Frame(input_panel, bg=self.panel_bg)
        pic_frame.pack(fill=tk.X, padx=10, pady=10)
        
        self.upload_pic_btn = tk.Button(
            pic_frame,
            text="📷 Upload Picture / Camera",
            command=self.open_camera,
            bg="#2d7a3e",
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=15,
            pady=8,
            cursor="hand2"
        )
        self.upload_pic_btn.pack(fill=tk.X)
        
        pic_desc = tk.Label(
            pic_frame,
            text="   - Block Diagram\n   - Circuit Diagram\n   - Handwritten Notes",
            font=("Segoe UI", 9),
            bg=self.panel_bg,
            fg="#b0b0b0",
            justify=tk.LEFT,
            anchor=tk.W
        )
        pic_desc.pack(fill=tk.X, pady=(5, 0))
        
        # Document upload section
        doc_frame = tk.Frame(input_panel, bg=self.panel_bg)
        doc_frame.pack(fill=tk.X, padx=10, pady=(10, 10))
        
        self.upload_doc_btn = tk.Button(
            doc_frame,
            text="📄 Upload Document",
            command=self.upload_document,
            bg="#007acc",
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=15,
            pady=8,
            cursor="hand2"
        )
        self.upload_doc_btn.pack(fill=tk.X)
        
        doc_desc = tk.Label(
            doc_frame,
            text="   - RTL Functionality Desc.\n   - Verification Requirements\n   - Design Specifications",
            font=("Segoe UI", 9),
            bg=self.panel_bg,
            fg="#b0b0b0",
            justify=tk.LEFT,
            anchor=tk.W
        )
        doc_desc.pack(fill=tk.X, pady=(5, 0))
        
        # Right: Output Options Panel
        output_panel = tk.LabelFrame(
            top_section,
            text="  OUTPUT OPTIONS  ",
            font=("Segoe UI", 11, "bold"),
            bg=self.panel_bg,
            fg=self.fg_color,
            relief=tk.GROOVE,
            bd=2
        )
        output_panel.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(5, 0))
        
        options_frame = tk.Frame(output_panel, bg=self.panel_bg)
        options_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        tk.Label(
            options_frame,
            text="⚙️  Convert to:",
            font=("Segoe UI", 10, "bold"),
            bg=self.panel_bg,
            fg=self.fg_color,
            anchor=tk.W
        ).pack(fill=tk.X, pady=(0, 10))
        
        # Radio buttons for output mode
        self.rb_markdown = tk.Radiobutton(
            options_frame,
            text="○ Markdown (.md)\n   └─ VSCode Copilot Context",
            variable=self.output_mode,
            value="markdown",
            font=("Segoe UI", 9),
            bg=self.panel_bg,
            fg=self.fg_color,
            selectcolor=self.panel_bg,
            activebackground=self.panel_bg,
            activeforeground=self.fg_color,
            anchor=tk.W,
            justify=tk.LEFT
        )
        self.rb_markdown.pack(fill=tk.X, pady=2)
        
        self.rb_rtl = tk.Radiobutton(
            options_frame,
            text="● RTL Design (.sv)\n   └─ Module + Interfaces",
            variable=self.output_mode,
            value="rtl",
            font=("Segoe UI", 9),
            bg=self.panel_bg,
            fg=self.fg_color,
            selectcolor=self.panel_bg,
            activebackground=self.panel_bg,
            activeforeground=self.fg_color,
            anchor=tk.W,
            justify=tk.LEFT
        )
        self.rb_rtl.pack(fill=tk.X, pady=2)
        
        self.rb_uvm = tk.Radiobutton(
            options_frame,
            text="○ UVM Verification Env\n   └─ Multiple Files:\n      • Test\n      • Scoreboard\n      • Sequences\n      • Agent/Driver/Monitor\n      • Coverage/Assertions",
            variable=self.output_mode,
            value="uvm",
            font=("Segoe UI", 9),
            bg=self.panel_bg,
            fg=self.fg_color,
            selectcolor=self.panel_bg,
            activebackground=self.panel_bg,
            activeforeground=self.fg_color,
            anchor=tk.W,
            justify=tk.LEFT
        )
        self.rb_uvm.pack(fill=tk.X, pady=2)
        
        # ========== INPUT PREVIEW ==========
        input_preview_panel = tk.LabelFrame(
            main_frame,
            text="  📤 INPUT PREVIEW  ",
            font=("Segoe UI", 10, "bold"),
            bg=self.panel_bg,
            fg=self.fg_color,
            relief=tk.GROOVE,
            bd=2,
            height=180
        )
        input_preview_panel.pack(fill=tk.X, expand=False, pady=(0, 10))
        input_preview_panel.pack_propagate(False)
        
        preview_container = tk.Frame(input_preview_panel, bg=self.panel_bg)
        preview_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        self.input_preview = tk.Label(
            preview_container,
            text="No input loaded\n\nUse 'Upload Picture' or 'Upload Document'\nto load content for processing",
            font=("Segoe UI", 10),
            bg=self.chat_bg,
            fg="#808080",
            justify=tk.CENTER
        )
        self.input_preview.pack(fill=tk.BOTH, expand=True)
        
        self.input_status = tk.Label(
            input_preview_panel,
            text="Status: No input",
            font=("Segoe UI", 8),
            bg=self.panel_bg,
            fg="#808080",
            anchor=tk.W
        )
        self.input_status.pack(fill=tk.X, padx=10, pady=(0, 5))
        
        # ========== ACTION BUTTONS ==========
        actions_panel = tk.LabelFrame(
            main_frame,
            text="  ACTIONS  ",
            font=("Segoe UI", 10, "bold"),
            bg=self.panel_bg,
            fg=self.fg_color,
            relief=tk.GROOVE,
            bd=2
        )
        actions_panel.pack(fill=tk.X, pady=(0, 10))
        
        actions_frame = tk.Frame(actions_panel, bg=self.panel_bg)
        actions_frame.pack(fill=tk.X, padx=10, pady=10)
        
        self.process_btn = tk.Button(
            actions_frame,
            text="🔄 Process",
            command=self.process_input,
            bg="#2d7a3e",
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=20,
            pady=8,
            cursor="hand2"
        )
        self.process_btn.pack(side=tk.LEFT, padx=5)
        
        self.view_results_btn = tk.Button(
            actions_frame,
            text="👁️ View Results",
            command=self.show_results_window,
            bg="#2d2d30",
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=20,
            pady=8,
            cursor="hand2",
            state=tk.DISABLED,
            disabledforeground="#5a5a5a"
        )
        self.view_results_btn.pack(side=tk.LEFT, padx=5)
        
        self.save_all_btn = tk.Button(
            actions_frame,
            text="💾 Save All Files",
            command=self.save_all_files,
            bg=self.button_bg,
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=20,
            pady=8,
            cursor="hand2"
        )
        self.save_all_btn.pack(side=tk.LEFT, padx=5)
        
        self.copy_btn = tk.Button(
            actions_frame,
            text="📋 Copy",
            command=self.copy_output,
            bg=self.button_bg,
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=20,
            pady=8,
            cursor="hand2"
        )
        self.copy_btn.pack(side=tk.LEFT, padx=5)
        
        self.clear_btn = tk.Button(
            actions_frame,
            text="🗑️ Clear",
            command=self.clear_all,
            bg="#8b0000",
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=20,
            pady=8,
            cursor="hand2"
        )
        self.clear_btn.pack(side=tk.LEFT, padx=5)
        
        # ========== PROCESSING LOG ==========
        log_panel = tk.LabelFrame(
            main_frame,
            text="  📜 PROCESSING LOG  ",
            font=("Segoe UI", 10, "bold"),
            bg=self.panel_bg,
            fg=self.fg_color,
            relief=tk.GROOVE,
            bd=2
        )
        log_panel.pack(fill=tk.X)
        
        self.log_display = scrolledtext.ScrolledText(
            log_panel,
            wrap=tk.WORD,
            font=("Consolas", 9),
            bg=self.chat_bg,
            fg=self.fg_color,
            insertbackground=self.fg_color,
            relief=tk.FLAT,
            padx=10,
            pady=10,
            height=3
        )
        self.log_display.pack(fill=tk.BOTH, expand=False, padx=10, pady=10)
        self.log_display.config(state=tk.DISABLED)
        
        # Log tags
        self.log_display.tag_config("success", foreground="#51cf66")
        self.log_display.tag_config("error", foreground="#ff6b6b")
        self.log_display.tag_config("processing", foreground="#ffa500")
        self.log_display.tag_config("info", foreground="#b0b0b0")
        
        # Display welcome message
        self.display_welcome_message()
        
    def display_welcome_message(self):
        """Display welcome message in log"""
        api_status = "✅ Connected" if self.agent.is_ready() else "❌ Not configured"
        
        self.add_log("info", "Application started successfully")
        if self.agent.is_ready():
            self.add_log("success", f"✓ AI Agent connected ({Config.AZURE_OPENAI_MODEL_NAME})")
        else:
            self.add_log("error", "❌ AI Agent not configured - check .env file")
    
    def open_chat_window(self):
        """Open a separate window for chatting with the AI agent"""
        # Create chat window
        chat_window = tk.Toplevel(self.root)
        chat_window.title("DVM Alchemist - Transform Designs to Code")
        chat_window.geometry("800x600")
        chat_window.configure(bg=self.bg_color)
        
        # Header
        header_frame = tk.Frame(chat_window, bg=self.bg_color)
        header_frame.pack(fill=tk.X, padx=10, pady=10)
        
        title_label = tk.Label(
            header_frame,
            text="🧙‍♂️ DVM Alchemist",
            font=("Segoe UI", 16, "bold"),
            bg=self.bg_color,
            fg=self.fg_color
        )
        title_label.pack(side=tk.LEFT)
        
        close_btn = tk.Button(
            header_frame,
            text="✖ Close",
            command=chat_window.destroy,
            bg="#8b0000",
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=15,
            pady=5,
            cursor="hand2"
        )
        close_btn.pack(side=tk.RIGHT)
        
        # Chat display
        chat_display = scrolledtext.ScrolledText(
            chat_window,
            wrap=tk.WORD,
            font=("Consolas", 10),
            bg=self.chat_bg,
            fg=self.fg_color,
            insertbackground=self.fg_color,
            relief=tk.FLAT,
            padx=15,
            pady=15
        )
        chat_display.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
        chat_display.config(state=tk.DISABLED)
        
        # Configure text tags
        chat_display.tag_config("user", foreground="#4ec9b0", font=("Consolas", 10, "bold"))
        chat_display.tag_config("agent", foreground="#569cd6", font=("Consolas", 10, "bold"))
        chat_display.tag_config("timestamp", foreground="#808080", font=("Consolas", 9))
        chat_display.tag_config("message", foreground="#d4d4d4")
        
        # Display welcome message in chat
        chat_display.config(state=tk.NORMAL)
        timestamp = datetime.now().strftime("%H:%M:%S")
        api_status = "✅ Connected" if self.agent.is_ready() else "❌ Not configured"
        welcome_text = f"""Welcome! I'm your DVM AI Assistant - the Alchemist of Design & Verification!

AI Status: {api_status} | Model: {Config.AZURE_OPENAI_MODEL_NAME}

Ready to help transform your designs into RTL and verification code!
You can ask me about:
- RTL design patterns and best practices
- UVM verification strategies
- SystemVerilog coding questions
- Design specifications and requirements"""
        
        chat_display.insert(tk.END, f"[{timestamp}] ", "timestamp")
        chat_display.insert(tk.END, "Agent: ", "agent")
        chat_display.insert(tk.END, f"{welcome_text}\n\n", "message")
        chat_display.see(tk.END)
        chat_display.config(state=tk.DISABLED)
        
        # Input area
        input_frame = tk.Frame(chat_window, bg=self.bg_color)
        input_frame.pack(fill=tk.X, padx=10, pady=(0, 10))
        
        input_text = tk.Text(
            input_frame,
            height=3,
            font=("Segoe UI", 10),
            bg=self.input_bg,
            fg=self.fg_color,
            insertbackground=self.fg_color,
            relief=tk.FLAT,
            padx=10,
            pady=8,
            wrap=tk.WORD
        )
        input_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        def send_chat_message(event=None):
            """Send message in chat window"""
            message = input_text.get("1.0", tk.END).strip()
            
            if not message:
                return "break" if event else None
            
            # Display user message
            chat_display.config(state=tk.NORMAL)
            timestamp = datetime.now().strftime("%H:%M:%S")
            chat_display.insert(tk.END, f"[{timestamp}] ", "timestamp")
            chat_display.insert(tk.END, "You: ", "user")
            chat_display.insert(tk.END, f"{message}\n\n", "message")
            chat_display.see(tk.END)
            chat_display.config(state=tk.DISABLED)
            
            # Clear input
            input_text.delete("1.0", tk.END)
            
            # Update status
            chat_display.config(state=tk.NORMAL)
            chat_display.insert(tk.END, f"[{datetime.now().strftime('%H:%M:%S')}] ", "timestamp")
            chat_display.insert(tk.END, "System: ", "agent")
            chat_display.insert(tk.END, "Processing...\n\n", "message")
            chat_display.see(tk.END)
            chat_display.config(state=tk.DISABLED)
            chat_window.update_idletasks()
            
            # Get agent response
            response = self.agent.get_response(message)
            
            # Display agent response
            chat_display.config(state=tk.NORMAL)
            # Remove "Processing..." line
            chat_display.delete("end-3l", "end-1l")
            timestamp = datetime.now().strftime("%H:%M:%S")
            chat_display.insert(tk.END, f"[{timestamp}] ", "timestamp")
            chat_display.insert(tk.END, "Agent: ", "agent")
            chat_display.insert(tk.END, f"{response}\n\n", "message")
            chat_display.see(tk.END)
            chat_display.config(state=tk.DISABLED)
            
            return "break" if event else None
        
        input_text.bind("<Return>", lambda e: send_chat_message(e) if not (e.state & 0x1) else None)
        input_text.bind("<Shift-Return>", lambda e: None)
        
        send_button = tk.Button(
            input_frame,
            text="Send",
            command=send_chat_message,
            bg=self.button_bg,
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=20,
            pady=8,
            cursor="hand2"
        )
        send_button.pack(side=tk.RIGHT, padx=(10, 0))
    
    def add_log(self, log_type, message):
        """Add a message to the processing log"""
        self.log_display.config(state=tk.NORMAL)
        timestamp = datetime.now().strftime("%H:%M:%S")
        self.log_display.insert(tk.END, f"[{timestamp}] {message}\n", log_type)
        self.log_display.see(tk.END)
        self.log_display.config(state=tk.DISABLED)
    
    def get_agent_response(self, user_message, image_data=None):
        """Get response from AI agent"""
        response = self.agent.get_response(user_message, image_data=image_data)
        return response
    
    def open_camera(self):
        """Open camera to capture an image"""
        self.add_log("processing", "⚡ Opening camera...")
        self.root.update_idletasks()
        
        try:
            # Create camera window
            camera_window = tk.Toplevel(self.root)
            camera_window.title("Camera Capture")
            camera_window.geometry("800x650")
            camera_window.configure(bg=self.bg_color)
            
            # Video display label
            video_label = tk.Label(camera_window, bg=self.bg_color)
            video_label.pack(pady=10)
            
            # Instructions
            instructions = tk.Label(
                camera_window,
                text="Position your diagram in the camera view and click 'Capture'",
                font=("Segoe UI", 10),
                bg=self.bg_color,
                fg=self.fg_color
            )
            instructions.pack(pady=5)
            
            # Button frame
            btn_frame = tk.Frame(camera_window, bg=self.bg_color)
            btn_frame.pack(pady=10)
            
            # Capture flag
            captured_image = {'data': None}
            
            # Initialize camera
            cap = cv2.VideoCapture(0)
            
            if not cap.isOpened():
                messagebox.showerror("Camera Error", "Could not access camera. Please check your camera connection.")
                camera_window.destroy()
                self.add_log("error", "❌ Camera not accessible")
                return
            
            self.add_log("success", "✓ Camera opened successfully")
            
            def update_frame():
                """Update video frame"""
                if cap.isOpened():
                    ret, frame = cap.read()
                    if ret:
                        # Convert BGR to RGB
                        frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                        
                        # Resize for display
                        display_frame = cv2.resize(frame_rgb, (640, 480))
                        
                        # Convert to PhotoImage
                        img = Image.fromarray(display_frame)
                        imgtk = ImageTk.PhotoImage(image=img)
                        
                        video_label.imgtk = imgtk
                        video_label.configure(image=imgtk)
                        
                        # Store current frame
                        captured_image['frame'] = frame_rgb
                        
                        # Schedule next update
                        video_label.after(10, update_frame)
            
            def capture_image():
                """Capture current frame"""
                if captured_image.get('frame') is not None:
                    frame = captured_image['frame']
                    
                    # Store captured image (make a copy to ensure it persists)
                    self.captured_image = frame.copy()
                    
                    # Create thumbnail for preview
                    thumb = Image.fromarray(frame)
                    thumb.thumbnail((300, 300))
                    self.captured_image_tk = ImageTk.PhotoImage(thumb)
                    
                    # Update input preview - keep reference
                    self.input_preview.config(image=self.captured_image_tk, text="")
                    self.input_preview.image = self.captured_image_tk  # Keep a reference
                    self.input_status.config(text="Status: ✓ Image loaded from camera", fg="#51cf66")
                    
                    # Close camera
                    cap.release()
                    camera_window.destroy()
                    
                    self.add_log("success", f"✓ Image captured successfully (size: {frame.shape})")
            
            def close_camera():
                """Close camera without capturing"""
                cap.release()
                camera_window.destroy()
                self.add_log("info", "Camera closed without capture")
            
            # Capture button
            capture_btn = tk.Button(
                btn_frame,
                text="📸 Capture",
                command=capture_image,
                bg="#2d7a3e",
                fg=self.fg_color,
                font=("Segoe UI", 11, "bold"),
                relief=tk.FLAT,
                padx=30,
                pady=10,
                cursor="hand2"
            )
            capture_btn.pack(side=tk.LEFT, padx=5)
            
            # Cancel button
            cancel_btn = tk.Button(
                btn_frame,
                text="Cancel",
                command=close_camera,
                bg="#8b0000",
                fg=self.fg_color,
                font=("Segoe UI", 11, "bold"),
                relief=tk.FLAT,
                padx=30,
                pady=10,
                cursor="hand2"
            )
            cancel_btn.pack(side=tk.LEFT, padx=5)
            
            # Handle window close
            camera_window.protocol("WM_DELETE_WINDOW", close_camera)
            
            # Start video feed
            update_frame()
            
        except Exception as e:
            messagebox.showerror("Camera Error", f"Error opening camera: {str(e)}")
            self.add_log("error", f"❌ Camera error: {str(e)}")
    
    def upload_document(self):
        """Upload a document file"""
        filetypes = [
            ("All supported", "*.pdf *.docx *.txt"),
            ("PDF files", "*.pdf"),
            ("Word files", "*.docx"),
            ("Text files", "*.txt"),
            ("All files", "*.*")
        ]
        
        filepath = filedialog.askopenfilename(
            title="Select Document",
            filetypes=filetypes
        )
        
        if filepath:
            self.add_log("info", f"Document selected: {filepath}")
            self.input_status.config(text=f"Status: ✓ Document loaded - {filepath.split('/')[-1]}", fg="#51cf66")
            # TODO: Implement document reading logic
    
    def extract_files_from_response(self, response):
        """Extract multiple files from AI response with code blocks"""
        files = {}
        
        # Pattern to match code blocks with filenames
        # Supports: ```systemverilog:filename.sv, ```verilog:filename.v, ```markdown:filename.md
        pattern = r'```(?:systemverilog|verilog|sv|markdown):([^\n]+)\n(.*?)```'
        matches = re.findall(pattern, response, re.DOTALL)
        
        if matches:
            for filename, content in matches:
                filename = filename.strip()
                content = content.strip()
                files[filename] = content
                self.add_log("info", f"  → Extracted: {filename} ({len(content)} chars)")
        else:
            # Fallback: Try to extract module definitions without explicit filename
            module_pattern = r'module\s+(\w+)'
            module_matches = re.findall(module_pattern, response)
            
            if module_matches:
                # Try to extract each module as a separate file
                for module_name in set(module_matches):
                    # Try to find the module block
                    module_block_pattern = rf'(module\s+{module_name}.*?endmodule)'
                    module_content = re.search(module_block_pattern, response, re.DOTALL)
                    if module_content:
                        filename = f"{module_name}.sv"
                        files[filename] = module_content.group(1).strip()
                        self.add_log("info", f"  → Extracted module: {filename}")
            else:
                # Last fallback: try generic code block
                generic_pattern = r'```(?:systemverilog|verilog|sv)?\n(.*?)```'
                generic_matches = re.findall(generic_pattern, response, re.DOTALL)
                if generic_matches:
                    for idx, content in enumerate(generic_matches, 1):
                        content = content.strip()
                        if content:
                            # Try to get module name from content
                            module_match = re.search(r'module\s+(\w+)', content)
                            if module_match:
                                filename = f"{module_match.group(1)}.sv"
                            else:
                                filename = f"design_{idx}.sv"
                            files[filename] = content
                            self.add_log("info", f"  → Extracted code block: {filename}")
        
        return files
    
    def process_input(self):
        """Process the captured image or uploaded document"""
        if self.captured_image is None:
            messagebox.showwarning("No Input", "Please capture an image or upload a document first.")
            self.add_log("error", "❌ No input to process")
            return
        
        self.add_log("processing", f"⚡ AI analysis in progress... Image shape: {self.captured_image.shape}")
        self.root.update_idletasks()
        
        # Use default prompt based on mode (no chat input anymore)
        mode_prompts = {
                "rtl": """Analyze this diagram and generate ONLY the SystemVerilog RTL code. 

CRITICAL INSTRUCTIONS:
- NO explanations, NO comments outside code, NO markdown text
- Return ONLY code wrapped in code blocks
- Format: ```systemverilog:filename.sv for each file
- Generate one or more .sv files depending on the design complexity

Example format:
```systemverilog:counter.sv
module counter(
    input logic clk,
    input logic rst_n,
    output logic [7:0] count
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= 8'h0;
        else
            count <= count + 1;
    end
endmodule
```

If multiple modules are needed, create separate files:
```systemverilog:module_name.sv
[code here]
```

RETURN ONLY CODE IN THIS FORMAT - NO OTHER TEXT.""",

                "markdown": """Analyze this diagram and create markdown documentation.

CRITICAL INSTRUCTIONS:
- Return ONLY the markdown content
- NO extra explanations before or after
- Format as: ```markdown:design_doc.md

Example:
```markdown:design_doc.md
# Design Documentation
[your markdown content]
```

RETURN ONLY IN THIS FORMAT.""",

                "uvm": """Analyze this diagram and generate ONLY the UVM verification environment code.

CRITICAL INSTRUCTIONS:
- NO explanations, NO markdown text outside code blocks
- Return ONLY code wrapped in: ```systemverilog:filename.sv
- Generate separate files for each UVM component:
  * tb_top.sv (testbench top)
  * test.sv (test sequences)
  * env.sv (environment)
  * scoreboard.sv
  * agent.sv
  * driver.sv
  * monitor.sv
  * sequences.sv
  * coverage.sv

Example format:
```systemverilog:tb_top.sv
[code]
```

```systemverilog:test.sv
[code]
```

RETURN ONLY CODE IN THIS FORMAT - NO OTHER TEXT."""
        }
        prompt = mode_prompts.get(self.output_mode.get(), mode_prompts["rtl"])
        self.add_log("info", f"Using default prompt for {self.output_mode.get().upper()} mode")
        
        try:
            # Convert image to base64
            self.add_log("info", "Converting image to base64...")
            _, buffer = cv2.imencode('.png', cv2.cvtColor(self.captured_image, cv2.COLOR_RGB2BGR))
            img_base64 = base64.b64encode(buffer).decode('utf-8')
            
            image_data = {
                'base64': img_base64,
                'media_type': 'image/png'
            }
            
            self.add_log("info", f"Image encoded (size: {len(img_base64)} bytes)")
            
            # Get agent response
            self.add_log("processing", f"⚡ Sending to AI agent to generate {self.output_mode.get().upper()} code...")
            response = self.get_agent_response(prompt, image_data=image_data)
            
            # Parse response to extract files
            self.add_log("info", "Parsing AI response for file extraction...")
            self.generated_files = self.extract_files_from_response(response)
            
            if self.generated_files:
                self.add_log("success", f"✓ Extracted {len(self.generated_files)} file(s): {', '.join(self.generated_files.keys())}")
                
                # Store output for display
                display_text = f"Generated {len(self.generated_files)} file(s):\n\n"
                for filename, content in self.generated_files.items():
                    display_text += f"{'='*60}\n"
                    display_text += f"FILE: {filename}\n"
                    display_text += f"{'='*60}\n"
                    display_text += f"{content}\n\n"
                
                self.generated_output = display_text
                
                # Enable view button with enhanced styling
                self.view_results_btn.config(
                    state=tk.NORMAL,
                    text=f"👁️ View {len(self.generated_files)} Generated File(s)\n\nClick to see results",
                    bg="#2d7a3e",
                    fg="#ffffff"
                )
            else:
                # No files extracted, show raw response
                self.add_log("info", "No files extracted, showing raw response")
                self.generated_output = response
                
                # Enable view button with enhanced styling
                self.view_results_btn.config(
                    state=tk.NORMAL,
                    text="👁️ View Generated Code",
                    bg="#2d7a3e",
                    fg="#ffffff"
                )
            
            self.add_log("success", f"✓ {self.output_mode.get().upper()} code generated successfully")
            
        except Exception as e:
            self.add_log("error", f"❌ Error processing image: {str(e)}")
            messagebox.showerror("Processing Error", f"Error processing image:\n{str(e)}")
    
    def save_all_files(self):
        """Save generated code to files"""
        if self.generated_files:
            # Multiple files - ask for directory
            directory = filedialog.askdirectory(
                title="Select Directory to Save All Files"
            )
            
            if directory:
                try:
                    saved_files = []
                    
                    for filename, content in self.generated_files.items():
                        filepath = os.path.join(directory, filename)
                        with open(filepath, 'w', encoding='utf-8') as f:
                            f.write(content)
                        saved_files.append(filename)
                        self.add_log("success", f"✓ Saved: {filename}")
                    
                    files_list = "\n".join(saved_files)
                    messagebox.showinfo(
                        "Success",
                        f"Successfully saved {len(saved_files)} file(s) to:\n{directory}\n\nFiles:\n{files_list}"
                    )
                    self.add_log("success", f"✓ All {len(saved_files)} files saved to: {directory}")
                    
                except Exception as e:
                    self.add_log("error", f"❌ Error saving files: {str(e)}")
                    messagebox.showerror("Error", f"Failed to save files:\n{str(e)}")
        else:
            # No extracted files - save raw output as single file
            if not self.generated_output:
                messagebox.showwarning("No Output", "No generated code to save.")
                return
            
            # Determine default extension based on mode
            ext_map = {
                "rtl": ".sv",
                "markdown": ".md",
                "uvm": ".sv"
            }
            default_ext = ext_map.get(self.output_mode.get(), ".txt")
            
            filepath = filedialog.asksaveasfilename(
                title="Save Generated Code",
                defaultextension=default_ext,
                filetypes=[
                    ("SystemVerilog", "*.sv"),
                    ("Verilog", "*.v"),
                    ("Markdown", "*.md"),
                    ("Text files", "*.txt"),
                    ("All files", "*.*")
                ]
            )
            
            if filepath:
                try:
                    with open(filepath, 'w', encoding='utf-8') as f:
                        f.write(self.generated_output)
                    self.add_log("success", f"✓ File saved: {filepath}")
                    messagebox.showinfo("Success", f"File saved successfully:\n{filepath}")
                except Exception as e:
                    self.add_log("error", f"❌ Error saving file: {str(e)}")
                    messagebox.showerror("Error", f"Failed to save file:\n{str(e)}")
    
    def copy_output(self):
        """Copy output to clipboard"""
        if not self.generated_output:
            messagebox.showwarning("No Output", "No generated code to copy.")
            return
        
        self.root.clipboard_clear()
        self.root.clipboard_append(self.generated_output)
        self.add_log("success", "✓ Output copied to clipboard")
        messagebox.showinfo("Success", "Output copied to clipboard!")
    
    def show_results_window(self):
        """Open a window to display generated results"""
        if not self.generated_output:
            messagebox.showinfo("No Results", "No generated code to display.")
            return
        
        # Create results window
        results_window = tk.Toplevel(self.root)
        results_window.title("Generated Code - DVM")
        results_window.geometry("1000x700")
        results_window.configure(bg=self.bg_color)
        
        # Header
        header_frame = tk.Frame(results_window, bg=self.bg_color)
        header_frame.pack(fill=tk.X, padx=10, pady=10)
        
        title_label = tk.Label(
            header_frame,
            text=f"Generated Files ({len(self.generated_files)} file(s))" if self.generated_files else "Generated Code",
            font=("Segoe UI", 16, "bold"),
            bg=self.bg_color,
            fg=self.fg_color
        )
        title_label.pack(side=tk.LEFT)
        
        # Close button
        close_btn = tk.Button(
            header_frame,
            text="✖ Close",
            command=results_window.destroy,
            bg="#8b0000",
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=15,
            pady=5,
            cursor="hand2"
        )
        close_btn.pack(side=tk.RIGHT)
        
        # File tabs if multiple files
        if self.generated_files and len(self.generated_files) > 0:
            # Create notebook for tabs
            notebook = ttk.Notebook(results_window)
            notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
            
            # Add tab for each file
            for filename, content in self.generated_files.items():
                tab_frame = tk.Frame(notebook, bg=self.chat_bg)
                notebook.add(tab_frame, text=filename)
                
                # Add text widget for this file
                text_widget = scrolledtext.ScrolledText(
                    tab_frame,
                    wrap=tk.WORD,
                    font=("Consolas", 10),
                    bg=self.chat_bg,
                    fg=self.fg_color,
                    insertbackground=self.fg_color,
                    relief=tk.FLAT,
                    padx=15,
                    pady=15
                )
                text_widget.pack(fill=tk.BOTH, expand=True)
                text_widget.insert("1.0", content)
                text_widget.config(state=tk.DISABLED)
        else:
            # Single text area for all output
            text_frame = tk.Frame(results_window, bg=self.bg_color)
            text_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
            
            text_widget = scrolledtext.ScrolledText(
                text_frame,
                wrap=tk.WORD,
                font=("Consolas", 10),
                bg=self.chat_bg,
                fg=self.fg_color,
                insertbackground=self.fg_color,
                relief=tk.FLAT,
                padx=15,
                pady=15
            )
            text_widget.pack(fill=tk.BOTH, expand=True)
            text_widget.insert("1.0", self.generated_output)
            text_widget.config(state=tk.DISABLED)
        
        # Action buttons at bottom
        button_frame = tk.Frame(results_window, bg=self.bg_color)
        button_frame.pack(fill=tk.X, padx=10, pady=(0, 10))
        
        copy_btn = tk.Button(
            button_frame,
            text="📋 Copy All",
            command=lambda: self.copy_output(),
            bg=self.button_bg,
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=20,
            pady=8,
            cursor="hand2"
        )
        copy_btn.pack(side=tk.LEFT, padx=5)
        
        save_btn = tk.Button(
            button_frame,
            text="💾 Save Files",
            command=self.save_all_files,
            bg="#2d7a3e",
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=20,
            pady=8,
            cursor="hand2"
        )
        save_btn.pack(side=tk.LEFT, padx=5)
    
    def clear_all(self):
        """Clear all inputs and outputs"""
        if messagebox.askyesno("Clear All", "Are you sure you want to clear all inputs and outputs?"):
            # Clear input
            self.captured_image = None
            self.captured_image_tk = None
            self.input_preview.config(image="", text="No input loaded\n\nUse 'Upload Picture' or 'Upload Document'\nto load content for processing")
            self.input_status.config(text="Status: No input", fg="#808080")
            
            # Clear output
            self.generated_files = {}
            self.generated_output = ""
            self.view_results_btn.config(
                state=tk.DISABLED,
                bg="#2d2d30",
                fg="#cccccc",
                text="👁️ View Results"
            )
            
            # Reset agent conversation
            self.agent.reset_conversation()
            
            self.add_log("info", "All inputs and outputs cleared")
            messagebox.showinfo("Success", "All cleared successfully!")
    
    def check_api_status(self):
        """Check and display API configuration status"""
        if not self.agent.is_ready():
            self.add_log("error", "⚠️ AI not configured - Please check .env file")
        else:
            self.add_log("success", f"✓ Ready - AI Connected ({Config.AZURE_OPENAI_MODEL_NAME})")



def main():
    """Main entry point for the application"""
    root = tk.Tk()
    app = DVMApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
