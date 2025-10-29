"""
DVM - Design/Verif Maker
Main application file with GUI interface for AI agent interaction
"""

import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog
from datetime import datetime
from agent import DVMAgent
from config import Config
from document_processor import DocumentProcessor
from verification_agents import AssertionSpecialist, CoverageSpecialist, RequirementsAnalyzer, CodeReviewer, SystemVerilogExpert
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
        
        # Initialize document processor and specialized agents
        self.doc_processor = DocumentProcessor()
        self.vision_processor = None  # Lazy load
        self.assertion_agent = AssertionSpecialist()
        self.coverage_agent = CoverageSpecialist()
        self.requirements_agent = RequirementsAnalyzer()
        self.reviewer_agent = CodeReviewer()
        self.sv_expert = SystemVerilogExpert()  # SystemVerilog/UVM expert
        
        # Vision processing toggle
        self.use_vision_filtering = tk.BooleanVar(value=False)
        # Expert review toggle
        self.use_expert_review = tk.BooleanVar(value=True)
        
        # State variables
        self.output_mode = tk.StringVar(value="rtl")  # rtl, markdown, uvm, assertions, covergroups
        self.captured_image = None
        self.captured_image_tk = None
        self.generated_files = {}
        self.generated_output = ""  # Store full output text
        self.current_file = None
        self.uploaded_document_path = None  # Store uploaded document path
        
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
        
        # Vision filtering checkbox
        vision_check = tk.Checkbutton(
            doc_frame,
            text="🔍 Use AI Vision Pre-filtering (Recommended)\n   └─ Analyze pages as images first to remove irrelevant content",
            variable=self.use_vision_filtering,
            font=("Segoe UI", 8),
            bg=self.panel_bg,
            fg="#ffa500",
            selectcolor=self.panel_bg,
            activebackground=self.panel_bg,
            activeforeground="#ffa500",
            anchor=tk.W,
            justify=tk.LEFT
        )
        vision_check.pack(fill=tk.X, pady=(5, 0))
        
        # Expert review checkbox
        expert_check = tk.Checkbutton(
            doc_frame,
            text="🎓 SystemVerilog/UVM Expert Review (Recommended)\n   └─ Production-quality review by SV/UVM expert",
            variable=self.use_expert_review,
            font=("Segoe UI", 8),
            bg=self.panel_bg,
            fg="#51cf66",
            selectcolor=self.panel_bg,
            activebackground=self.panel_bg,
            activeforeground="#51cf66",
            anchor=tk.W,
            justify=tk.LEFT
        )
        expert_check.pack(fill=tk.X, pady=(2, 0))
        
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
        
        # Assertions option
        self.rb_assertions = tk.Radiobutton(
            options_frame,
            text="○ Assertions (.sv)\n   └─ SVA Properties",
            variable=self.output_mode,
            value="assertions",
            font=("Segoe UI", 9),
            bg=self.panel_bg,
            fg=self.fg_color,
            selectcolor=self.panel_bg,
            activebackground=self.panel_bg,
            activeforeground=self.fg_color,
            anchor=tk.W,
            justify=tk.LEFT
        )
        self.rb_assertions.pack(fill=tk.X, pady=2)
        
        # Covergroups option
        self.rb_covergroups = tk.Radiobutton(
            options_frame,
            text="○ Covergroups (.sv)\n   └─ Functional Coverage",
            variable=self.output_mode,
            value="covergroups",
            font=("Segoe UI", 9),
            bg=self.panel_bg,
            fg=self.fg_color,
            selectcolor=self.panel_bg,
            activebackground=self.panel_bg,
            activeforeground=self.fg_color,
            anchor=tk.W,
            justify=tk.LEFT
        )
        self.rb_covergroups.pack(fill=tk.X, pady=2)
        
        # UVM Verification Environment (complete package)
        self.rb_uvm = tk.Radiobutton(
            options_frame,
            text="○ UVM Verification Env\n   └─ Full Package (TB Top, Test, Env,\n       Scoreboard, Sequences, Agent,\n       Driver, Monitor)",
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
        log_panel.pack(fill=tk.BOTH, expand=True)
        
        self.log_display = scrolledtext.ScrolledText(
            log_panel,
            wrap=tk.WORD,
            font=("Consolas", 9),
            bg=self.chat_bg,
            fg=self.fg_color,
            insertbackground=self.fg_color,
            relief=tk.FLAT,
            padx=10,
            pady=10
        )
        self.log_display.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
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
            ("All supported", "*.pdf *.docx *.txt *.md"),
            ("PDF files", "*.pdf"),
            ("Word files", "*.docx"),
            ("Text files", "*.txt"),
            ("Markdown files", "*.md"),
            ("All files", "*.*")
        ]
        
        filepath = filedialog.askopenfilename(
            title="Select Document",
            filetypes=filetypes
        )
        
        if filepath:
            self.add_log("processing", f"⚡ Loading document: {os.path.basename(filepath)}")
            self.root.update_idletasks()
            
            try:
                # Read and preview document
                from document_processor import DocumentReader
                content, file_type = DocumentReader.read_file(filepath)
                
                # Store document path
                self.uploaded_document_path = filepath
                
                # Create preview (first 500 chars)
                preview_text = content[:500] + "..." if len(content) > 500 else content
                
                # Update preview
                self.input_preview.config(
                    text=preview_text,
                    font=("Consolas", 8),
                    justify=tk.LEFT,
                    anchor=tk.NW
                )
                
                self.input_status.config(
                    text=f"Status: ✓ Document loaded - {os.path.basename(filepath)} ({file_type}, {len(content)} chars)",
                    fg="#51cf66"
                )
                
                self.add_log("success", f"✓ Document loaded successfully ({len(content)} characters)")
                
            except Exception as e:
                self.add_log("error", f"❌ Error loading document: {str(e)}")
                messagebox.showerror("Document Error", f"Failed to load document:\n{str(e)}")
                self.uploaded_document_path = None
    
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
        # Check if we have document input (for assertions/covergroups)
        if self.uploaded_document_path and self.output_mode.get() in ['assertions', 'covergroups']:
            self.process_document_for_verification()
            return
        
        # Otherwise, require image input
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

                "assertions": """Analyze this diagram and generate ONLY SystemVerilog assertions (SVA).

CRITICAL INSTRUCTIONS:
- NO explanations, NO markdown text outside code blocks
- Return ONLY assertion code wrapped in: ```systemverilog:assertions.sv
- Generate only SystemVerilog assertions and properties
- Focus on protocol checking and functional verification

Example format:
```systemverilog:assertions.sv
property p_req_ack;
    @(posedge clk) disable iff (!rst_n)
    req |-> ##[1:3] ack;
endproperty

assert property (p_req_ack) else $error("Request not acknowledged");
```

RETURN ONLY ASSERTION CODE IN THIS FORMAT - NO OTHER TEXT.""",

                "covergroups": """Analyze this diagram and generate ONLY SystemVerilog covergroups.

CRITICAL INSTRUCTIONS:
- NO explanations, NO markdown text outside code blocks
- Return ONLY coverage code wrapped in: ```systemverilog:coverage.sv
- Generate only covergroups, coverpoints, and cross coverage
- Focus on functional coverage based on the design

Example format:
```systemverilog:coverage.sv
covergroup cg_example @(posedge clk);
    cp_signal: coverpoint signal {
        bins low = {[0:7]};
        bins high = {[8:15]};
    }
    cross_coverage: cross cp_signal, other_signal;
endgroup
```

RETURN ONLY COVERAGE CODE IN THIS FORMAT - NO OTHER TEXT.""",

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

RETURN ONLY IN THIS FORMAT."""
        }
        
        # For UVM mode, generate complete verification environment
        if self.output_mode.get() == "uvm":
            mode_prompts["uvm"] = """Analyze this diagram and generate a COMPLETE UVM verification environment.

CRITICAL INSTRUCTIONS:
- NO explanations, NO markdown text outside code blocks
- Return ONLY code wrapped in: ```systemverilog:filename.sv
- Generate ALL UVM components (complete package):
  * tb_top.sv - Testbench top module
  * test.sv - UVM test
  * env.sv - UVM environment
  * scoreboard.sv - UVM scoreboard
  * sequences.sv - UVM sequences
  * agent.sv - UVM agent
  * driver.sv - UVM driver
  * monitor.sv - UVM monitor

Example format:
```systemverilog:tb_top.sv
[code]
```

```systemverilog:test.sv
[code]
```

RETURN ONLY CODE IN THIS FORMAT - NO OTHER TEXT. Generate ALL 8 components."""
        
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
    
    def process_document_for_verification(self):
        """Process uploaded document for assertions or covergroups generation"""
        artifact_type = self.output_mode.get()
        use_vision = self.use_vision_filtering.get()
        
        if use_vision:
            self.add_log("processing", f"⚡ Processing document with VISION PRE-FILTERING for {artifact_type.upper()}...")
            self.add_log("info", "━━━ Vision-First AI Analysis Pipeline ━━━")
        else:
            self.add_log("processing", f"⚡ Processing document for {artifact_type.upper()} generation...")
            self.add_log("info", "━━━ Enhanced AI Analysis Pipeline ━━━")
        
        self.root.update_idletasks()
        
        try:
            if use_vision:
                # ========== VISION-FIRST PIPELINE ==========
                self._process_with_vision_filtering(artifact_type)
            else:
                # ========== STANDARD PIPELINE ==========
                self._process_with_text_analysis(artifact_type)
                
        except Exception as e:
            self.add_log("error", f"❌ Error processing document: {str(e)}")
            import traceback
            traceback.print_exc()
            messagebox.showerror("Processing Error", f"Error processing document:\n{str(e)}")
    
    def _process_with_vision_filtering(self, artifact_type: str):
        """Process document using vision-first approach"""
        # Lazy load vision processor
        if self.vision_processor is None:
            self.add_log("info", "� Initializing vision processor (first time)...")
            from vision_document_processor import VisionDocumentProcessor
            self.vision_processor = VisionDocumentProcessor()
        
        # Step 1: Convert pages to images and analyze with vision
        self.add_log("info", "👁️ Step 1/7: Converting document pages to images...")
        self.root.update_idletasks()
        
        vision_result = self.vision_processor.process_document_with_vision(
            self.uploaded_document_path,
            artifact_type
        )
        
        total_pages = vision_result['total_pages']
        relevant_pages = vision_result['relevant_pages']
        discarded_pages = vision_result['discarded_pages']
        
        self.add_log("success", f"✓ Analyzed {total_pages} pages with AI vision")
        self.add_log("info", f"  📊 Kept: {relevant_pages} pages | Discarded: {discarded_pages} pages ({discarded_pages/total_pages*100:.1f}% filtered)")
        
        # Show top relevant pages
        if relevant_pages > 0:
            self.add_log("info", "  Top relevant pages:")
            for page_info in vision_result['filtered_page_data'][:3]:
                analysis = page_info['analysis']
                hints = ', '.join(analysis.get('key_hints', [])[:3])
                self.add_log("info", f"    Page {analysis['page_number']}: Score {analysis['score']}/10 - {hints}")
        
        if relevant_pages == 0:
            self.add_log("error", "❌ No relevant pages found! Try disabling vision filtering.")
            messagebox.showerror("No Content", "Vision analysis found no relevant pages.\nTry unchecking 'Use AI Vision Pre-filtering'.")
            return
        
        # Step 2: Extract text from filtered pages only
        self.add_log("processing", "📄 Step 2/7: Extracting text from filtered pages...")
        self.root.update_idletasks()
        
        filtered_text = self.vision_processor.extract_text_from_filtered_pages(vision_result)
        self.add_log("success", f"✓ Extracted {len(filtered_text)} characters from {relevant_pages} pages")
        
        # Step 3: Prepare vision-filtered context
        self.add_log("info", "📋 Step 3/7: Preparing vision-filtered context...")
        self.root.update_idletasks()
        
        context = self.vision_processor.prepare_vision_context(vision_result)
        context_size = len(context)
        self.add_log("success", f"✓ Context prepared ({context_size} chars, {relevant_pages} pages)")
        
        # Continue with standard processing from step 4
        self._continue_standard_processing(artifact_type, context, vision_result=vision_result)
    
    def _process_with_text_analysis(self, artifact_type: str):
        """Process document using standard text analysis"""
        # Step 1: Process document to find relevant sections
        self.add_log("info", "📄 Step 1/6: Analyzing document structure and content...")
        self.root.update_idletasks()
        
        processing_result = self.doc_processor.process_document(
            self.uploaded_document_path,
            artifact_type
        )
        
        relevant_count = len(processing_result['relevant_sections'])
        total_sections = processing_result['total_chunks']
        self.add_log("success", f"✓ Analyzed {total_sections} sections, found {relevant_count} potentially relevant section(s)")
        
        # Display top scores
        if relevant_count > 0:
            top_3 = processing_result['relevant_sections'][:3]
            for i, sec in enumerate(top_3, 1):
                chunk = sec['chunk']
                # Show hierarchical path if available
                if chunk.get('full_path'):
                    location = chunk['full_path']
                else:
                    location = chunk['title']
                self.add_log("info", f"  #{i}: '{location}' (Score: {sec['score']:.2%})")
        
        # Step 1.5: AI Validation (optional but recommended)
        self.add_log("processing", "🤖 Step 2/6: AI validation of section relevance...")
        self.root.update_idletasks()
        
        try:
            from ai_validator import AIValidator
            validator = AIValidator()
            validated_sections = validator.validate_and_rerank_sections(
                processing_result['relevant_sections'],
                artifact_type,
                max_validate=min(5, relevant_count)  # Validate top 5
            )
            processing_result['relevant_sections'] = validated_sections
            
            # Show AI-validated scores
            self.add_log("success", "✓ AI validation completed - sections re-ranked")
            if len(validated_sections) > 0:
                top_validated = validated_sections[0]
                if 'ai_validation' in top_validated:
                    ai_info = top_validated['ai_validation']
                    self.add_log("info", f"  Top section reason: {ai_info.get('reason', 'N/A')[:80]}")
                    
        except Exception as e:
            self.add_log("info", f"  ⚠️ AI validation skipped: {str(e)[:50]}")
        
        # Step 2: Prepare context for requirements analysis
        self.add_log("info", "📋 Step 3/6: Preparing enhanced context with extracted entities...")
        self.root.update_idletasks()
        
        context = self.doc_processor.prepare_context_for_agent(processing_result)
        context_size = len(context)
        self.add_log("success", f"✓ Context prepared ({context_size} chars)")
        
        # Continue with standard processing
        self._continue_standard_processing(artifact_type, context)
    
    def _continue_standard_processing(self, artifact_type: str, context: str, vision_result=None):
        """Continue processing from context preparation step"""
        use_expert = self.use_expert_review.get()
        step_offset = 3 if vision_result else 3
        total_steps = 8 if (vision_result and use_expert) else (7 if vision_result or use_expert else 6)
        
        # Step N: Analyze requirements with specialist agent
        self.add_log("processing", f"⚡ Step {step_offset+1}/{total_steps}: Extracting {artifact_type} requirements with AI...")
        self.root.update_idletasks()
        
        analysis = self.requirements_agent.analyze_document(context, artifact_type)
        requirements = analysis['analysis']
        
        req_lines = len(requirements.split('\n'))
        self.add_log("success", f"✓ Requirements extracted successfully ({req_lines} lines)")
        
        # Step N+1: Generate verification code with specialized agent
        self.add_log("processing", f"⚡ Step {step_offset+2}/{total_steps}: Generating {artifact_type} code with specialist...")
        self.root.update_idletasks()
        
        if artifact_type == 'assertions':
            generated_code = self.assertion_agent.generate_assertions(requirements)
        else:  # covergroups
            generated_code = self.coverage_agent.generate_covergroups(requirements)
        
        code_lines = len(generated_code.split('\n'))
        self.add_log("success", f"✓ {artifact_type.capitalize()} code generated ({code_lines} lines)")
        
        # Step N+2: Basic review and refine code
        self.add_log("processing", f"⚡ Step {step_offset+3}/{total_steps}: Basic code review and refinement...")
        self.root.update_idletasks()
        
        review = self.reviewer_agent.review_code(generated_code, requirements, artifact_type)
        
        # Check if improvements are needed
        if "IMPROVEMENTS:" in review and len(review.split("IMPROVEMENTS:")[1].strip()) > 50:
            self.add_log("info", "  🔧 Applying suggested improvements...")
            self.root.update_idletasks()
            refined_code = self.reviewer_agent.refine_code(generated_code, review)
            final_code = refined_code
            self.add_log("success", "  ✓ Code improved based on review")
        else:
            final_code = generated_code
            self.add_log("success", "  ✓ Code passed review without changes needed")
        
        # Step N+3: Expert SystemVerilog/UVM review (if enabled)
        if use_expert:
            self.add_log("processing", f"⚡ Step {step_offset+4}/{total_steps}: SystemVerilog/UVM Expert Review...")
            self.add_log("info", "  🎓 Engaging Senior SV/UVM Expert for production-quality review...")
            self.root.update_idletasks()
            
            expert_review = self.sv_expert.expert_review(final_code, artifact_type, requirements)
            
            # Parse expert score
            import re
            score_match = re.search(r'SCORE:\s*(\d+)/10', expert_review)
            if score_match:
                score = int(score_match.group(1))
                self.add_log("info", f"  📊 Expert Score: {score}/10")
                
                # If score < 8, apply expert improvements
                if score < 8:
                    self.add_log("info", f"  🔧 Applying expert improvements (score: {score}/10)...")
                    self.root.update_idletasks()
                    expert_improved = self.sv_expert.improve_code(final_code, expert_review, artifact_type)
                    final_code = expert_improved
                    self.add_log("success", "  ✓ Code enhanced by SV/UVM expert")
                else:
                    self.add_log("success", f"  ✓ Code meets production standards (score: {score}/10)")
            else:
                # No score found, but apply improvements anyway
                self.add_log("info", "  🔧 Applying expert refinements...")
                self.root.update_idletasks()
                expert_improved = self.sv_expert.improve_code(final_code, expert_review, artifact_type)
                final_code = expert_improved
                self.add_log("success", "  ✓ Code enhanced by SV/UVM expert")
        
        # Parse generated code to extract files
        self.add_log("info", "📦 Extracting generated files...")
        self.generated_files = self.extract_files_from_response(final_code)
        
        if self.generated_files:
            self.add_log("success", f"✓ Generated {len(self.generated_files)} file(s): {', '.join(self.generated_files.keys())}")
            
            # Store output for display with analysis info
            if vision_result:
                display_text = f"Generated {len(self.generated_files)} file(s) from VISION-FILTERED document:\n\n"
                display_text += f"📄 Document: {os.path.basename(self.uploaded_document_path)}\n"
                display_text += f"� Vision Analysis: {vision_result['relevant_pages']}/{vision_result['total_pages']} pages kept\n"
            else:
                display_text = f"Generated {len(self.generated_files)} file(s) from enhanced document analysis:\n\n"
                display_text += f"📄 Document: {os.path.basename(self.uploaded_document_path)}\n"
            
            display_text += f"{'='*60}\n\n"
            
            for filename, content in self.generated_files.items():
                display_text += f"{'='*60}\n"
                display_text += f"FILE: {filename}\n"
                display_text += f"{'='*60}\n"
                display_text += f"{content}\n\n"
            
            self.generated_output = display_text
            
            # Enable view button
            self.view_results_btn.config(
                state=tk.NORMAL,
                text=f"👁️ View {len(self.generated_files)} Generated File(s)",
                bg="#2d7a3e",
                fg="#ffffff"
            )
        else:
            # Fallback to raw output
            self.generated_output = final_code
            self.view_results_btn.config(
                state=tk.NORMAL,
                text="👁️ View Generated Code",
                bg="#2d7a3e",
                fg="#ffffff"
            )
        
        # Build pipeline description
        pipeline_features = []
        if vision_result:
            pipeline_features.append("VISION-FILTERED")
        if use_expert:
            pipeline_features.append("EXPERT-REVIEWED")
        
        pipeline_name = " + ".join(pipeline_features) if pipeline_features else "STANDARD"
        self.add_log("success", f"━━━ ✅ {pipeline_name} {artifact_type.upper()} GENERATION COMPLETED! ━━━")
    
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
                "assertions": ".sv",
                "covergroups": ".sv",
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
            self.uploaded_document_path = None
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
            
            # Reset all agents
            self.agent.reset_conversation()
            self.assertion_agent.reset_conversation()
            self.coverage_agent.reset_conversation()
            self.requirements_agent.reset_conversation()
            self.reviewer_agent.reset_conversation()
            
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
