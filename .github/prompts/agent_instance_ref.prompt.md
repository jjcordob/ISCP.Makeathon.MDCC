---
mode: Vibe_code_assistant
---

# MDCC - Agent Instance Reference
 
 ## Agent Configuration example

 This is just an example of the API call, you can configure it as needed

``python
client = AzureOpenAI(
    api_version="2024-12-01-preview",
    azure_endpoint="https://genai-proxy.intel.com/api",
    api_key=os.getenv("AZURE_OPENAI_KEY", "ADD_TOKEN_HERE"),
    http_client=httpx.Client(verify=False),
)


response = client.chat.completions.create(
    messages=[
        {"role": "system", "content": "You are a helpful assistant."},
        {"role": "user", "content": "I am going to Paris, what should I see?"}
    ],
    max_completion_tokens=512,
    temperature=1.0,
    top_p=1.0,
    frequency_penalty=0.0,
    presence_penalty=0.0,
    model=claude_sonnet_4_5,
)
```