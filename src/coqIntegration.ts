import * as vscode from 'vscode';
import * as childProcess from 'child_process';

// Interface for tracked states
export interface TrackedState {
    id: string; // Unique identifier for the state
    text: string; // Will now store only the current line
    fullText: string; // New field to store the full text for Coq
    theoremName: string;
    lineOffset: number;
    characterOffset: number;
    coqResult?: string; // Optional Coq result
    linkedStateIds: string[]; // IDs of states linked to this one
}

// Array to store tracked states
export const trackedStates: TrackedState[] = [];

/**
 * Extract text before the cursor position
 */
export function extractTextBeforeCursor(editor: vscode.TextEditor): string {
    const position = editor.selection.active;
    const document = editor.document;

    // Get all text from the beginning of the document up to the cursor position
    let text = '';

    // Add all lines before the current line
    for (let i = 0; i < position.line; i++) {
        text += document.lineAt(i).text + '\n';
    }

    // Add the current line up to the cursor position
    text += document.lineAt(position.line).text.substring(0, position.character);

    return text;
}

export function extractTextBeforeCursorForUpdate(
    editor: vscode.TextEditor,
    theoremName: string,
    lineOffset: number,
    characterOffset: number
): string {
    const document = editor.document;

    // Find the theorem start line
    let theoremStartLine = 0;
    for (let i = 0; i < document.lineCount; i++) {
        const line = document.lineAt(i);
        if (line.text.includes(theoremName)) {
            theoremStartLine = i;
            break;
        }
    }

    // Calculate the actual line and character position
    const actualLine = theoremStartLine + lineOffset;
    const actualCharacter = characterOffset;

    // Extract text up to the cursor position
    let text = '';
    for (let i = 0; i < actualLine; i++) {
        text += document.lineAt(i).text + '\n';
    }
    text += document.lineAt(actualLine).text.substring(0, actualCharacter);

    return text;
}

/**
 * Extract only the current line text
 */
export function extractCurrentLineText(editor: vscode.TextEditor): string {
    const position = editor.selection.active;
    const line = editor.document.lineAt(position.line);
    return line.text;
}

/**
 * Find the theorem name from the current position
 */
export function findTheoremName(editor: vscode.TextEditor): string {
    const position = editor.selection.active;
    const document = editor.document;

    // Start from the current line and go backwards
    for (let i = position.line; i >= 0; i--) {
        const line = document.lineAt(i);
        const text = line.text;

        // Look for theorem or lemma declarations
        const theoremMatch = text.match(/\b(Theorem|Lemma)\s+([a-zA-Z0-9_]+)/);
        if (theoremMatch) {
            return theoremMatch[2]; // Return the theorem name
        }
    }

    return "Unknown Theorem";
}

/**
 * Calculate line and character offset from the beginning of the theorem
 */
export function calculateOffsets(editor: vscode.TextEditor): { lineOffset: number, characterOffset: number } {
    const position = editor.selection.active;
    const document = editor.document;

    // Find the theorem start line
    let theoremStartLine = 0;
    for (let i = position.line; i >= 0; i--) {
        const line = document.lineAt(i);
        const text = line.text;

        if (text.match(/\b(Theorem|Lemma)\s+([a-zA-Z0-9_]+)/)) {
            theoremStartLine = i;
            break;
        }
    }

    // Calculate offsets
    const lineOffset = position.line - theoremStartLine;

    // Character offset is now simply the cursor position on the current line
    const characterOffset = position.character;

    return { lineOffset, characterOffset };
}

/**
 * Send code to Coq and get the result
 */
export async function sendCodeToCoq(code: string): Promise<string> {
    return new Promise((resolve) => {
        console.log('Starting Coq');
        const process = childProcess.spawn('coqtop', []);
        console.log('Coq started');
        console.log('Code: ' + code);
        let result = '';
        const lines = code.split('\n').filter(line => line.trim());

        // Collect the last output only
        process.stdout!.on('data', (data: Buffer) => {
            console.log(`Coq Output: ${data}`);
            result = data.toString(); // Overwrite with the latest chunk
        });

        for (const line of lines) {
            console.log(line);
            process.stdin!.write(line.trim() + '\n', (err) => {
                if (err) {
                    console.error(err);
                }
            });
        }

        setTimeout(() => {
            process.kill();
            resolve(result.trim()); // Resolve with the last captured output
        }, 1000);
    });
}

/**
 * Track a state from the current editor position
 */
export async function trackState(editor: vscode.TextEditor): Promise<TrackedState> {
    // Extract only the current line text for the state
    const currentLineText = extractCurrentLineText(editor);

    // Extract full text before cursor for Coq
    const fullText = extractTextBeforeCursor(editor);

    // Find theorem name
    const theoremName = findTheoremName(editor);

    // Calculate offsets
    const { lineOffset, characterOffset } = calculateOffsets(editor);

    // Create tracked state
    const state: TrackedState = {
        id: generateUniqueId(), // Generate a unique ID for this state
        text: currentLineText, // Store only the current line
        fullText: fullText, // Store the full text for Coq
        theoremName,
        lineOffset,
        characterOffset,
        linkedStateIds: [] // Initialize with no linked states
    };

    // Add to tracked states array
    trackedStates.push(state);

    // Send to Coq using the full text
    try {
        const coqResult = await sendCodeToCoq(fullText);
        console.log(`Coq result for state: ${coqResult}`);

        // Store the Coq result in the state
        state.coqResult = coqResult;
    } catch (error) {
        console.error(`Error sending to Coq: ${error}`);
        state.coqResult = `Error: ${error}`;
    }

    return state;
}

/**
 * Generate a unique ID for a state
 */
function generateUniqueId(): string {
    return Date.now().toString(36) + Math.random().toString(36).substring(2);
}

/**
 * Link two states together
 */
export function linkStates(sourceStateId: string, targetStateId: string): boolean {
    const sourceState = trackedStates.find(state => state.id === sourceStateId);
    const targetState = trackedStates.find(state => state.id === targetStateId);

    if (!sourceState || !targetState) {
        return false;
    }

    // Add the target state ID to the source state's linked states if not already linked
    if (!sourceState.linkedStateIds.includes(targetStateId)) {
        sourceState.linkedStateIds.push(targetStateId);
    }

    return true;
}

/**
 * Unlink two states
 */
export function unlinkStates(sourceStateId: string, targetStateId: string): boolean {
    const sourceState = trackedStates.find(state => state.id === sourceStateId);

    if (!sourceState) {
        return false;
    }

    // Remove the target state ID from the source state's linked states
    sourceState.linkedStateIds = sourceState.linkedStateIds.filter(id => id !== targetStateId);

    return true;
}