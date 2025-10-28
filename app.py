"""
MDCC - Multimedia Design Code Converter
Main application file with GUI interface for AI agent interaction
"""

import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog
from datetime import datetime
from agent import MDCCAgent
from config import Config
import cv2
import base64
from PIL import Image, ImageTk
import io


class MDCCApp:
    """Main application class for MDCC with chat interface"""
    
    def __init__(self, root):
        self.root = root
        self.root.title("MDCC - Multimedia Design Code Converter")
        self.root.geometry("900x700")
        self.root.minsize(700, 500)
        
        # Initialize AI agent
        self.agent = MDCCAgent()
        
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
        
        # Configure root background
        self.root.configure(bg=self.bg_color)
        
    def create_widgets(self):
        """Create and layout all UI widgets"""
        # Main container
        main_frame = tk.Frame(self.root, bg=self.bg_color)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Title
        title_label = tk.Label(
            main_frame,
            text="MDCC - AI Agent Chat",
            font=("Segoe UI", 16, "bold"),
            bg=self.bg_color,
            fg=self.fg_color
        )
        title_label.pack(pady=(0, 10))
        
        # Chat display area
        chat_frame = tk.Frame(main_frame, bg=self.bg_color)
        chat_frame.pack(fill=tk.BOTH, expand=True)
        
        # Scrolled text for chat history
        self.chat_display = scrolledtext.ScrolledText(
            chat_frame,
            wrap=tk.WORD,
            font=("Consolas", 10),
            bg=self.chat_bg,
            fg=self.fg_color,
            insertbackground=self.fg_color,
            relief=tk.FLAT,
            padx=10,
            pady=10
        )
        self.chat_display.pack(fill=tk.BOTH, expand=True)
        self.chat_display.config(state=tk.DISABLED)
        
        # Configure text tags for styling
        self.chat_display.tag_config("user", foreground="#4ec9b0", font=("Consolas", 10, "bold"))
        self.chat_display.tag_config("agent", foreground="#569cd6", font=("Consolas", 10, "bold"))
        self.chat_display.tag_config("timestamp", foreground="#808080", font=("Consolas", 8))
        self.chat_display.tag_config("message", foreground="#d4d4d4")
        
        # Input area
        input_frame = tk.Frame(main_frame, bg=self.bg_color)
        input_frame.pack(fill=tk.X, pady=(10, 0))
        
        # Input text box
        self.input_text = tk.Text(
            input_frame,
            height=4,
            font=("Segoe UI", 10),
            bg=self.input_bg,
            fg=self.fg_color,
            insertbackground=self.fg_color,
            relief=tk.FLAT,
            padx=10,
            pady=10,
            wrap=tk.WORD
        )
        self.input_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.input_text.bind("<Return>", self.handle_send_message)
        self.input_text.bind("<Shift-Return>", lambda e: None)  # Allow Shift+Enter for new line
        
        # Send button
        button_frame = tk.Frame(input_frame, bg=self.bg_color)
        button_frame.pack(side=tk.RIGHT, padx=(10, 0))
        
        # Camera button
        self.camera_button = tk.Button(
            button_frame,
            text="📷 Camera",
            command=self.open_camera,
            bg="#2d7a3e",
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=15,
            pady=10,
            cursor="hand2"
        )
        self.camera_button.pack(pady=(0, 5))
        
        self.send_button = tk.Button(
            button_frame,
            text="Send",
            command=self.send_message,
            bg=self.button_bg,
            fg=self.fg_color,
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=20,
            pady=10,
            cursor="hand2"
        )
        self.send_button.pack()
        
        # Status bar
        self.status_bar = tk.Label(
            main_frame,
            text="Ready",
            font=("Segoe UI", 9),
            bg=self.bg_color,
            fg="#808080",
            anchor=tk.W
        )
        self.status_bar.pack(fill=tk.X, pady=(10, 0))
        
        # Welcome message
        self.display_welcome_message()
        
    def display_welcome_message(self):
        """Display welcome message in chat"""
        api_status = "✅ Connected" if self.agent.is_ready() else "❌ Not configured"
        
        welcome_text = f"""Welcome to MDCC - Multimedia Design Code Converter!

I'm your AI assistant powered by Azure OpenAI. I can help you convert hand-drawn diagrams, notes, and sketches into:
• RTL code (Verilog/SystemVerilog/VHDL)
• Verification environments (testbenches, assertions, covergroups)

AI Status: {api_status}
Model: {Config.AZURE_OPENAI_MODEL_NAME}

How can I assist you today?
"""
        self.add_message("Agent", welcome_text)
        
    def handle_send_message(self, event):
        """Handle Enter key press to send message"""
        if event.state & 0x1:  # Check if Shift is pressed
            return  # Allow Shift+Enter to insert new line
        else:
            self.send_message()
            return "break"  # Prevent default Enter behavior
            
    def send_message(self):
        """Send user message and get agent response"""
        message = self.input_text.get("1.0", tk.END).strip()
        
        if not message:
            return
            
        # Display user message
        self.add_message("You", message)
        
        # Clear input
        self.input_text.delete("1.0", tk.END)
        
        # Update status
        self.status_bar.config(text="Processing...")
        self.root.update_idletasks()
        
        # Get agent response (placeholder for now)
        response = self.get_agent_response(message)
        
        # Display agent response
        self.add_message("Agent", response)
        
        # Update status
        self.status_bar.config(text="Ready")
        
    def get_agent_response(self, user_message):
        """
        Get response from AI agent
        """
        # Use the AI agent to get response
        response = self.agent.get_response(user_message)
        return response
        
    def add_message(self, sender, message):
        """Add a message to the chat display"""
        self.chat_display.config(state=tk.NORMAL)
        
        # Add timestamp
        timestamp = datetime.now().strftime("%H:%M:%S")
        self.chat_display.insert(tk.END, f"[{timestamp}] ", "timestamp")
        
        # Add sender
        tag = "user" if sender == "You" else "agent"
        self.chat_display.insert(tk.END, f"{sender}: ", tag)
        
        # Add message
        self.chat_display.insert(tk.END, f"{message}\n\n", "message")
        
        # Scroll to bottom
        self.chat_display.see(tk.END)
        
        self.chat_display.config(state=tk.DISABLED)
    
    def open_camera(self):
        """Open camera to capture an image"""
        self.status_bar.config(text="Opening camera...")
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
                self.status_bar.config(text="Ready")
                return
            
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
                    # Convert to base64
                    frame = captured_image['frame']
                    _, buffer = cv2.imencode('.png', cv2.cvtColor(frame, cv2.COLOR_RGB2BGR))
                    img_base64 = base64.b64encode(buffer).decode('utf-8')
                    
                    captured_image['data'] = img_base64
                    
                    # Close camera
                    cap.release()
                    camera_window.destroy()
                    
                    # Send to agent
                    self.process_captured_image(img_base64)
            
            def close_camera():
                """Close camera without capturing"""
                cap.release()
                camera_window.destroy()
                self.status_bar.config(text="Ready")
            
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
            self.status_bar.config(text="Ready")
    
    def process_captured_image(self, img_base64):
        """Process captured image and send to agent"""
        self.status_bar.config(text="Processing image...")
        self.root.update_idletasks()
        
        # Add user message
        self.add_message("You", "📷 [Image captured from camera]")
        
        # Get prompt from user
        prompt = self.input_text.get("1.0", tk.END).strip()
        if not prompt:
            prompt = "Please analyze this diagram and generate the corresponding RTL code or verification environment."
        
        # Clear input
        self.input_text.delete("1.0", tk.END)
        
        # Prepare image data
        image_data = {
            'base64': img_base64,
            'media_type': 'image/png'
        }
        
        # Get agent response
        response = self.agent.get_response(prompt, image_data=image_data)
        
        # Display response
        self.add_message("Agent", response)
        
        self.status_bar.config(text="Ready")
    
    def check_api_status(self):
        """Check and display API configuration status"""
        if not self.agent.is_ready():
            self.status_bar.config(
                text="⚠️ AI not configured - Please check .env file",
                fg="#ff6b6b"
            )
        else:
            self.status_bar.config(
                text=f"Ready - AI Connected ✓ ({Config.AZURE_OPENAI_MODEL_NAME})", 
                fg="#51cf66"
            )


def main():
    """Main entry point for the application"""
    root = tk.Tk()
    app = MDCCApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
