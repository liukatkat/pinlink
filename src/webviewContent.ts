import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { trackedStates, linkStates, unlinkStates, extractTextBeforeCursorForUpdate, sendCodeToCoq } from './coqIntegration';

/**
 * Get the HTML content for the webview
 */
export function getWebviewContent(context: vscode.ExtensionContext): string {
    // Get the paths to the webview resources
    const htmlPath = path.join(context.extensionPath, 'src', 'webview', 'index.html');
    const cssPath = path.join(context.extensionPath, 'src', 'webview', 'styles.css');
    const scriptPath = path.join(context.extensionPath, 'src', 'webview', 'script.js');

    // Read the HTML file
    let html = fs.readFileSync(htmlPath, 'utf8');

    // Read the CSS file
    const css = fs.readFileSync(cssPath, 'utf8');

    // Read the JavaScript file
    const script = fs.readFileSync(scriptPath, 'utf8');

    // Replace the CSS link with inline CSS
    html = html.replace('<link rel="stylesheet" href="styles.css">', `<style>${css}</style>`);

    // Replace the script tag with inline script
    html = html.replace('<script src="script.js"></script>', `<script>${script}</script>`);

    return html;
}

/**
 * Create and return a webview panel for the sidebar
 */
export function createSidebarPanel(context: vscode.ExtensionContext): vscode.WebviewPanel {
    const sidebarPanel = vscode.window.createWebviewPanel(
        'pinlinkSidebar', // Identifies the type of the webview panel
        'PinLink', // Title of the panel displayed to the user
        vscode.ViewColumn.Two, // Show in the second column (sidebar)
        {
            enableScripts: true, // Enable JavaScript in the webview
            retainContextWhenHidden: true, // Keep the webview content in memory when hidden
        }
    );

    // Set the HTML content for the webview
    sidebarPanel.webview.html = getWebviewContent(context);

    return sidebarPanel;
}

/**
 * Set up message handling for the webview
 */
export function setupWebviewMessageHandling(webview: vscode.Webview, context: vscode.ExtensionContext): void {
    webview.onDidReceiveMessage(
        async (message) => {
            switch (message.command) {
                case 'alert':
                    vscode.window.showInformationMessage(message.text);
                    return;
                case 'getStates':
                    // Send the current states to the webview
                    webview.postMessage({
                        command: 'updateStates',
                        states: trackedStates
                    });
                    return;
                case 'linkStates':
                    // Link two states
                    const success = linkStates(message.sourceStateId, message.targetStateId);
                    if (success) {
                        // Update the webview with the new states
                        webview.postMessage({
                            command: 'updateStates',
                            states: trackedStates
                        });
                    } else {
                        vscode.window.showErrorMessage('Failed to link states.');
                    }
                    return;
                case 'unlinkStates':
                    // Unlink two states
                    const unlinkSuccess = unlinkStates(message.sourceStateId, message.targetStateId);
                    if (unlinkSuccess) {
                        // Update the webview with the new states
                        webview.postMessage({
                            command: 'updateStates',
                            states: trackedStates
                        });
                    } else {
                        vscode.window.showErrorMessage('Failed to unlink states.');
                    }
                    return;
                case 'navigateToState':
                    // Navigate to the state in the editor
                    navigateToState(message.theoremName, message.lineOffset, message.characterOffset);
                    return;
                case 'refreshStates':
                    // Refresh each state by sending its code to Coq again
                    for (const state of trackedStates) {
                        const editor = vscode.window.visibleTextEditors.find((e) =>
                            e.document.getText().includes(state.theoremName)
                        );

                        if (editor) {
                            const fullText = extractTextBeforeCursorForUpdate(editor, state.theoremName, state.lineOffset, state.characterOffset);
                            try {
                                const coqResult = await sendCodeToCoq(fullText);
                                state.coqResult = coqResult;
                            } catch (error) {
                                state.coqResult = `Error: ${error}`;
                            }
                        }
                    }

                    // Update the webview with the refreshed states
                    webview.postMessage({
                        command: 'updateStates',
                        states: trackedStates
                    });
                    return;
            }
        },
        undefined,
        context.subscriptions
    );
}

/**
 * Navigate to a state in the editor
 */
function navigateToState(theoremName: string, lineOffset: number, characterOffset: number): void {
    // Find all open text editors
    const editors = vscode.window.visibleTextEditors;

    if (editors.length === 0) {
        vscode.window.showInformationMessage('No open editors to navigate to.');
        return;
    }

    // Try to find the editor containing the theorem
    let targetEditor: vscode.TextEditor | undefined;
    let theoremStartLine: number = -1;

    for (const editor of editors) {
        const document = editor.document;
        const text = document.getText();

        // Check if the document contains the theorem name
        if (text.includes(theoremName)) {
            targetEditor = editor;

            // Find the line where the theorem starts
            for (let i = 0; i < document.lineCount; i++) {
                const line = document.lineAt(i);
                if (line.text.includes(theoremName)) {
                    theoremStartLine = i;
                    break;
                }
            }

            break;
        }
    }

    // If no editor contains the theorem, use the active editor
    if (!targetEditor) {
        targetEditor = vscode.window.activeTextEditor;
    }

    if (targetEditor) {
        // Calculate the actual line number by adding the theorem start line to the offset
        const actualLine = theoremStartLine >= 0 ? theoremStartLine + lineOffset : lineOffset;

        // Make sure the line is within bounds
        const line = Math.min(Math.max(0, actualLine), targetEditor.document.lineCount - 1);

        // Get the line text to ensure character offset is valid
        const lineText = targetEditor.document.lineAt(line).text;
        const char = Math.min(characterOffset, lineText.length);

        // Create the position
        const position = new vscode.Position(line, char);

        // Reveal the line in the editor
        targetEditor.revealRange(new vscode.Range(position, position), vscode.TextEditorRevealType.InCenter);

        // Set the cursor position
        targetEditor.selection = new vscode.Selection(position, position);

        // Focus the editor
        vscode.window.showTextDocument(targetEditor.document, { viewColumn: targetEditor.viewColumn, preserveFocus: false });
    }
}

/**
 * Webview provider class for the PinLink sidebar
 */
export class PinLinkWebviewProvider implements vscode.WebviewViewProvider {
    private _view?: vscode.WebviewView;

    constructor(private readonly context: vscode.ExtensionContext) { }

    resolveWebviewView(
        webviewView: vscode.WebviewView,
        context: vscode.WebviewViewResolveContext,
        _token: vscode.CancellationToken,
    ) {
        this._view = webviewView;

        // Set the webview content
        webviewView.webview.options = {
            enableScripts: true,
            localResourceRoots: []
        };

        // Set the HTML content
        webviewView.webview.html = getWebviewContent(this.context);

        // Set up message handling
        setupWebviewMessageHandling(webviewView.webview, this.context);

        // Send initial states
        webviewView.webview.postMessage({
            command: 'updateStates',
            states: trackedStates
        });
    }

    // Method to update the webview with new states
    public updateStates() {
        if (this._view) {
            this._view.webview.postMessage({
                command: 'updateStates',
                states: trackedStates
            });
        }
    }
}