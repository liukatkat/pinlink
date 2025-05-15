// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as vscode from 'vscode';
import * as path from 'path';
import { PinLinkWebviewProvider } from './webviewContent';
import { trackState } from './coqIntegration';

// Store the webview provider reference
let webviewProvider: PinLinkWebviewProvider | undefined;

// This method is called when your extension is activated
// Your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {

	// Use the console to output diagnostic information (console.log) and errors (console.error)
	// This line of code will only be executed once when your extension is activated
	console.log('Congratulations, your extension "pinlink" is now active!');

	// Register the webview provider
	webviewProvider = new PinLinkWebviewProvider(context);
	context.subscriptions.push(
		vscode.window.registerWebviewViewProvider('pinlink.webview', webviewProvider)
	);

	// Register the trackState command
	const trackStateCommand = vscode.commands.registerCommand('pinlink.trackState', async () => {
		// Get the active text editor
		const editor = vscode.window.activeTextEditor;
		if (editor) {
			try {
				// Track the state
				const state = await trackState(editor);

				// Show a message with the tracked state
				vscode.window.showInformationMessage(`Tracked state: "${state.text.substring(0, 30)}${state.text.length > 30 ? '...' : ''}" from ${state.theoremName}`);

				// Update the webview with the new state
				if (webviewProvider) {
					webviewProvider.updateStates();
				}
			} catch (error) {
				vscode.window.showErrorMessage(`Error tracking state: ${error}`);
			}
		} else {
			vscode.window.showInformationMessage('No active editor');
		}
	});

	context.subscriptions.push(trackStateCommand);
}

// This method is called when your extension is deactivated
export function deactivate() { }