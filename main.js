const palette = [
	{ id: "triangle", sides: 3, radius: 56 },
	{ id: "square", sides: 4, radius: 52 },
	{ id: "pentagon", sides: 5, radius: 55 },
	{ id: "hexagon", sides: 6, radius: 58 },
	{ id: "octagon", sides: 8, radius: 62 },
];

const COLOR_CHOICES = ["#ef4444", "#f97316", "#facc15", "#22c55e", "#06b6d4", "#3b82f6", "#8b5cf6", "#ec4899"];
const DEFAULT_SHAPE_FILL = "#c5cad4";
const DEFAULT_SHAPE_STROKE = "#646d7d";
const VERTEX_SNAP_DISTANCE = 13;
const EDGE_SNAP_DISTANCE = 16;
const EDGE_ANGLE_TOLERANCE_DEG = 10;
const WORKSPACES_PER_RULE = 2;

const paletteById = new Map(palette.map((item) => [item.id, item]));
const controlsEl = document.getElementById("spawn-controls");
const clearBtn = document.getElementById("clear-btn");
const clearAllBtn = document.getElementById("clear-all-btn");
const rotateLeftBtn = document.getElementById("rotate-left-btn");
const rotateRightBtn = document.getElementById("rotate-right-btn");
const scaleDownBtn = document.getElementById("scale-down-btn");
const scaleUpBtn = document.getElementById("scale-up-btn");
const saveBtn = document.getElementById("save-btn");
const loadBtn = document.getElementById("load-btn");
const loadInput = document.getElementById("load-input");
const colorControlsEl = document.getElementById("color-controls");
const rulesContainerEl = document.getElementById("rules-container");
const outputWorkspaceEl = document.getElementById("output-workspace");
const applyRulesBtn = document.getElementById("apply-rules-btn");
const resetOutputBtn = document.getElementById("reset-output-btn");
const addRuleButtonEl = document.createElement("button");

const STORAGE_RULES_SNAPSHOT_KEY = "fracdle.rules.snapshot.v2";
const STORAGE_OUTPUT_ORIGINAL_KEY = "fracdle.output.original.v2";

const sandboxes = [];
const rules = [];
const colorSwatchButtons = [];
let activeSandbox = null;
let outputSandbox = null;
let ruleCount = 0;
let shapeClipboard = [];

const MIN_SHAPE_SCALE = 0.35;
const MAX_SHAPE_SCALE = 8;
const SCALE_STEP_UP = 1.15;
const SCALE_STEP_DOWN = 1 / SCALE_STEP_UP;

let isApplyingRules = false;

function regularPolygonVertices(sides, radius) {
	const points = [];
	const step = (Math.PI * 2) / sides;
	const rotationOffset = sides === 4 ? -Math.PI / 4 : 0;
	for (let i = 0; i < sides; i += 1) {
		const angle = step * i - Math.PI / 2 + rotationOffset;
		points.push({ x: Math.cos(angle) * radius, y: Math.sin(angle) * radius });
	}
	return points;
}

function toKonvaPointArray(vertices) {
	return vertices.flatMap((v) => [v.x, v.y]);
}

function degToRad(deg) {
	return (deg * Math.PI) / 180;
}

function clamp(value, min, max) {
	return Math.max(min, Math.min(max, value));
}

function hexToRgb(hex) {
	const normalizedHex = hex.replace("#", "");
	const value = Number.parseInt(normalizedHex, 16);
	if (Number.isNaN(value) || normalizedHex.length !== 6) {
		return { r: 100, g: 109, b: 125 };
	}
	return { r: (value >> 16) & 255, g: (value >> 8) & 255, b: value & 255 };
}

function rgbToHex({ r, g, b }) {
	const toHex = (n) => n.toString(16).padStart(2, "0");
	return `#${toHex(r)}${toHex(g)}${toHex(b)}`;
}

function darkenHex(hex, amount = 0.35) {
	const rgb = hexToRgb(hex);
	return rgbToHex({
		r: clamp(Math.round(rgb.r * (1 - amount)), 0, 255),
		g: clamp(Math.round(rgb.g * (1 - amount)), 0, 255),
		b: clamp(Math.round(rgb.b * (1 - amount)), 0, 255),
	});
}

function normalized(vec) {
	const len = Math.hypot(vec.x, vec.y);
	return len ? { x: vec.x / len, y: vec.y / len } : { x: 0, y: 0 };
}

function transformLocalPointToWorld(localPoint, group) {
	const angle = degToRad(group.rotation());
	const cos = Math.cos(angle);
	const sin = Math.sin(angle);
	const sx = group.scaleX() || 1;
	const sy = group.scaleY() || 1;
	const scaledX = localPoint.x * sx;
	const scaledY = localPoint.y * sy;
	const worldX = scaledX * cos - scaledY * sin + group.x();
	const worldY = scaledX * sin + scaledY * cos + group.y();
	return { x: worldX, y: worldY };
}

class Sandbox {
	constructor(containerEl, options = {}) {
		this.containerEl = containerEl;
		this.shapes = [];
		this.nonShadowShapeCount = 0;
		this.selectedShapeId = null;
		this.selectedShapeIds = new Set();
		this.maxShapes = Number.isFinite(options.maxShapes) ? options.maxShapes : Infinity;
		this.onShapesChanged = typeof options.onShapesChanged === "function" ? options.onShapesChanged : null;
		this.canSpawnShape = typeof options.canSpawnShape === "function" ? options.canSpawnShape : null;
		this.canChangeShapeColor =
			typeof options.canChangeShapeColor === "function" ? options.canChangeShapeColor : null;

		this.stage = new Konva.Stage({
			container: containerEl,
			width: containerEl.clientWidth,
			height: containerEl.clientHeight,
		});

		this.layer = new Konva.Layer();
		this.stage.add(this.layer);

		this.stage.on("mousedown touchstart", (event) => {
			if (event.target === this.stage) {
				this.setSelectedShape(null);
			}
			setActiveSandbox(this);
		});

		this.layer.draw();
	}

	notifyShapesChanged() {
		if (typeof this.onShapesChanged === "function") {
			this.onShapesChanged(this);
		}
	}

	setShapesChangedHandler(handler) {
		this.onShapesChanged = typeof handler === "function" ? handler : null;
	}

	setActive(active) {
		this.containerEl.style.boxShadow = active ? "inset 0 0 0 3px #ff6f3c66" : "inset 0 0 0 1px #e5e9f1";
	}

	resize() {
		this.stage.width(this.containerEl.clientWidth);
		this.stage.height(this.containerEl.clientHeight);
		this.layer.batchDraw();
	}

	getShapeById(shapeId) {
		return this.shapes.find((shape) => shape.id === shapeId) || null;
	}

	setShapeColor(shape, fillColor) {
		shape.fillColor = fillColor;
		shape.strokeColor = darkenHex(fillColor, 0.4);
		shape.polygon.fill(shape.fillColor);
		shape.polygon.stroke(shape.strokeColor);
		shape.markers.forEach((marker) => marker.stroke(shape.strokeColor));
	}

	updateShapeMarkerVisuals(shape, selected = false) {
		const groupScale = shape.group.scaleX() || 1;
		const inverseScale = groupScale !== 0 ? 1 / groupScale : 1;
		const smallScaleFactor = groupScale < 1 ? groupScale : 1;
		shape.markers.forEach((marker, idx) => {
			const markerKind = shape.markerKinds?.[idx] || "corner";
			if (markerKind === "corner") {
				marker.radius(selected ? 5 : 4);
			} else {
				marker.radius(selected ? 4 : 3);
			}
			marker.scaleX(inverseScale * smallScaleFactor);
			marker.scaleY(inverseScale * smallScaleFactor);
		});
	}

	setSelectedShape(shapeId) {
		if (shapeId == null) {
			this.selectedShapeId = null;
			this.selectedShapeIds.clear();
		} else {
			this.selectedShapeId = shapeId;
			this.selectedShapeIds = new Set([shapeId]);
		}
		this.applySelectionVisuals();
	}

	toggleSelectedShape(shapeId) {
		if (!shapeId) {
			return;
		}
		if (this.selectedShapeIds.has(shapeId)) {
			this.selectedShapeIds.delete(shapeId);
		} else {
			this.selectedShapeIds.add(shapeId);
		}
		this.selectedShapeId = this.selectedShapeIds.has(shapeId)
			? shapeId
			: this.selectedShapeIds.values().next().value || null;
		this.applySelectionVisuals();
	}

	setSelectedShapes(shapeIds) {
		this.selectedShapeIds = new Set(shapeIds.filter(Boolean));
		this.selectedShapeId = this.selectedShapeIds.values().next().value || null;
		this.applySelectionVisuals();
	}

	getSelectedShapes() {
		if (this.selectedShapeIds.size === 0) {
			return [];
		}
		return this.shapes.filter((shape) => this.selectedShapeIds.has(shape.id));
	}

	applySelectionVisuals() {
		this.shapes.forEach((shape) => {
			const selected = this.selectedShapeIds.has(shape.id);
			shape.polygon.strokeWidth(selected ? 5 : 3);
			this.updateShapeMarkerVisuals(shape, selected);
		});
		if (activeSandbox === this) {
			updateColorButtonState();
		}
		this.layer.batchDraw();
	}

	worldVertices(shape) {
		return shape.vertices.map((v) => transformLocalPointToWorld(v, shape.group));
	}

	worldSnapPoints(shape) {
		const points = Array.isArray(shape.anchorPoints) && shape.anchorPoints.length > 0 ? shape.anchorPoints : shape.vertices;
		return points.map((p) => transformLocalPointToWorld(p, shape.group));
	}

	snapScaleAnyVertexToNearbyVertex(activeShape, activeLocalPoint, anchorLocalPoint, anchorWorld, proposedScale) {
		if (!activeShape || !activeLocalPoint || !anchorLocalPoint || !anchorWorld) {
			return proposedScale;
		}

		const angle = degToRad(activeShape.group.rotation());
		const cos = Math.cos(angle);
		const sin = Math.sin(angle);

		let best = null;

		const localDelta = {
			x: activeLocalPoint.x - anchorLocalPoint.x,
			y: activeLocalPoint.y - anchorLocalPoint.y,
		};
		const deltaLenSq = localDelta.x * localDelta.x + localDelta.y * localDelta.y;
		if (deltaLenSq < 0.000001) {
			return proposedScale;
		}

		const candidatePoints = Array.isArray(activeShape.anchorPoints) && activeShape.anchorPoints.length > 0
			? activeShape.anchorPoints
			: activeShape.vertices;

		for (const activePoint of candidatePoints) {
			const pinnedDistance = Math.hypot(activePoint.x - anchorLocalPoint.x, activePoint.y - anchorLocalPoint.y);
			if (pinnedDistance < 0.001) {
				continue;
			}
			const pointDelta = {
				x: activePoint.x - anchorLocalPoint.x,
				y: activePoint.y - anchorLocalPoint.y,
			};
			const worldDeltaScaleOne = {
				x: pointDelta.x * cos - pointDelta.y * sin,
				y: pointDelta.x * sin + pointDelta.y * cos,
			};
			const pointLenSq = worldDeltaScaleOne.x * worldDeltaScaleOne.x + worldDeltaScaleOne.y * worldDeltaScaleOne.y;
			if (pointLenSq < 0.000001) {
				continue;
			}

			const proposedWorld = {
				x: anchorWorld.x + worldDeltaScaleOne.x * proposedScale,
				y: anchorWorld.y + worldDeltaScaleOne.y * proposedScale,
			};

			for (const candidateShape of this.shapes) {
				if (
					candidateShape.id === activeShape.id ||
					(candidateShape.isShadow && candidateShape.shadowKind !== "base-shadow")
				) {
					continue;
				}
				const candidatePoints = this.worldSnapPoints(candidateShape);
				for (const candidateVertex of candidatePoints) {
					const pinnedCandidateDistance = Math.hypot(
						candidateVertex.x - anchorWorld.x,
						candidateVertex.y - anchorWorld.y,
					);
					if (pinnedCandidateDistance < 0.001) {
						continue;
					}
					const distanceToProposed = Math.hypot(
						candidateVertex.x - proposedWorld.x,
						candidateVertex.y - proposedWorld.y,
					);
					if (distanceToProposed > VERTEX_SNAP_DISTANCE) {
						continue;
					}

					const rel = {
						x: candidateVertex.x - anchorWorld.x,
						y: candidateVertex.y - anchorWorld.y,
					};
					const projectedScale =
						(rel.x * worldDeltaScaleOne.x + rel.y * worldDeltaScaleOne.y) / pointLenSq;
					const clampedScale = clamp(projectedScale, MIN_SHAPE_SCALE, MAX_SHAPE_SCALE);
					const snappedWorld = {
						x: anchorWorld.x + worldDeltaScaleOne.x * clampedScale,
						y: anchorWorld.y + worldDeltaScaleOne.y * clampedScale,
					};
					const snapError = Math.hypot(
						candidateVertex.x - snappedWorld.x,
						candidateVertex.y - snappedWorld.y,
					);
					if (snapError > VERTEX_SNAP_DISTANCE) {
						continue;
					}

					if (!best || snapError < best.error) {
						best = { scale: clampedScale, error: snapError };
					}
				}
			}
		}

		return best ? best.scale : proposedScale;
	}

	worldEdges(shape) {
		const vertices = this.worldVertices(shape);
		const edges = [];
		for (let i = 0; i < vertices.length; i += 1) {
			const a = vertices[i];
			const b = vertices[(i + 1) % vertices.length];
			edges.push({
				midpoint: { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 },
				dir: normalized({ x: b.x - a.x, y: b.y - a.y }),
			});
		}
		return edges;
	}

	deleteShapeById(shapeId) {
		const index = this.shapes.findIndex((shape) => shape.id === shapeId);
		if (index < 0) {
			return false;
		}
		const [shape] = this.shapes.splice(index, 1);
		if (!shape.isShadow) {
			this.nonShadowShapeCount = Math.max(0, this.nonShadowShapeCount - 1);
		}
		shape.group.destroy();
		this.selectedShapeIds.delete(shapeId);
		if (this.selectedShapeId === shapeId) {
			this.selectedShapeId = this.selectedShapeIds.values().next().value || null;
		}
		if (activeSandbox === this) {
			updateColorButtonState();
		}
		this.layer.batchDraw();
		this.notifyShapesChanged();
		return true;
	}

	spawnShape(config, options = {}) {
		const isShadow = Boolean(options.isShadow);
		const isReadOnly = Boolean(options.isReadOnly);
		if (!isShadow && this.canSpawnShape && !this.canSpawnShape(config, options)) {
			return null;
		}
		if (!isShadow && this.nonShadowShapeCount >= this.maxShapes) {
			return null;
		}

		const vertices = regularPolygonVertices(config.sides, config.radius);
		const edgeMidpoints = [];
		for (let i = 0; i < vertices.length; i += 1) {
			const a = vertices[i];
			const b = vertices[(i + 1) % vertices.length];
			edgeMidpoints.push({
				x: (a.x + b.x) / 2,
				y: (a.y + b.y) / 2,
			});
		}
		const centerPoint = { x: 0, y: 0 };
		const anchorPoints = [...vertices, ...edgeMidpoints, centerPoint];
		const markerKinds = [
			...vertices.map(() => "corner"),
			...edgeMidpoints.map(() => "edge-midpoint"),
			"center",
		];
		const group = new Konva.Group({
			x: options.x ?? 70 + Math.random() * Math.max(30, this.stage.width() - 140),
			y: options.y ?? 70 + Math.random() * Math.max(30, this.stage.height() - 140),
			rotation: options.rotation ?? 0,
			scaleX: Number.isFinite(Number(options.scale)) ? Number(options.scale) : 1,
			scaleY: Number.isFinite(Number(options.scale)) ? Number(options.scale) : 1,
			draggable: !isShadow && !isReadOnly,
			listening: !isShadow && !isReadOnly,
		});

		const polygon = new Konva.Line({
			points: toKonvaPointArray(vertices),
			closed: true,
			fill: DEFAULT_SHAPE_FILL,
			stroke: DEFAULT_SHAPE_STROKE,
			strokeWidth: 3,
			lineJoin: "round",
			...(isReadOnly ? {} : {
				shadowColor: "#1f2633",
				shadowBlur: 8,
				shadowOffset: { x: 0, y: 2 },
				shadowOpacity: isShadow ? 0.08 : 0.2,
			}),
			opacity: isShadow ? 0.4 : 1,
		});
		group.add(polygon);

		const arrowTailY = config.radius * 0.2;
		const arrowHeadY = -config.radius * 0.45;
		const orientationArrow = new Konva.Arrow({
			x: 0,
			y: 0,
			points: [0, arrowTailY, 0, arrowHeadY],
			pointerLength: Math.max(6, config.radius * 0.14),
			pointerWidth: Math.max(6, config.radius * 0.14),
			stroke: "#1f2633",
			fill: "#1f2633",
			strokeWidth: 2,
			opacity: isShadow ? 0.14 : 0.2,
			listening: false,
		});
		group.add(orientationArrow);

		const markers = isReadOnly ? [] : anchorPoints.map((v, idx) => {
			const markerKind = markerKinds[idx];
			const marker = new Konva.Circle({
				x: v.x,
				y: v.y,
				radius: isShadow ? 3 : markerKind === "corner" ? 4 : 3,
				fill: markerKind === "corner" ? "#ffffff" : "#e7ebf4",
				stroke: DEFAULT_SHAPE_STROKE,
				strokeWidth: 2,
				listening: false,
				opacity: isShadow ? 0.28 : markerKind === "corner" ? 1 : 0.85,
			});
			group.add(marker);
			return marker;
		});

		const shapeModel = {
			id: `${config.id}-${crypto.randomUUID()}`,
			typeId: config.id,
			group,
			polygon,
			markers,
			vertices,
			anchorPoints,
			markerKinds,
			fillColor: DEFAULT_SHAPE_FILL,
			strokeColor: DEFAULT_SHAPE_STROKE,
			isShadow,
			shadowKind: options.shadowKind || null,
			dragMode: "move",
			dragScaleHandleKind: null,
			dragActiveLocalPoint: null,
			dragVertexIndex: -1,
			dragEdgeMidpointIndex: -1,
			dragAnchorVertexIndex: -1,
			dragAnchorLocalPoint: null,
			dragAnchorWorld: null,
			dragStartPos: null,
			dragStartScale: 1,
			dragStartPointerDistance: 0,
		};

		if (typeof options.fillColor === "string") {
			this.setShapeColor(shapeModel, options.fillColor);
		}
		this.updateShapeMarkerVisuals(shapeModel, false);

		if (!isShadow && !isReadOnly) {
			group.on("mousedown touchstart", (event) => {
				event.cancelBubble = true;
				setActiveSandbox(this);
				const additiveSelect = Boolean(event.evt?.shiftKey || event.evt?.ctrlKey || event.evt?.metaKey);
				if (additiveSelect) {
					this.toggleSelectedShape(shapeModel.id);
					return;
				}
				this.setSelectedShape(shapeModel.id);

				shapeModel.dragMode = "move";
				shapeModel.dragScaleHandleKind = null;
				shapeModel.dragActiveLocalPoint = null;
				shapeModel.dragVertexIndex = -1;
				shapeModel.dragEdgeMidpointIndex = -1;
				shapeModel.dragAnchorVertexIndex = -1;
				shapeModel.dragAnchorLocalPoint = null;
				shapeModel.dragAnchorWorld = null;
				const pointer = this.stage.getPointerPosition();
				if (pointer) {
					const sideCount = shapeModel.vertices.length;
					const localPoint = group.getAbsoluteTransform().copy().invert().point(pointer);
					for (let i = 0; i < shapeModel.vertices.length; i += 1) {
						const vertex = shapeModel.vertices[i];
						const dx = localPoint.x - vertex.x;
						const dy = localPoint.y - vertex.y;
						if (Math.hypot(dx, dy) <= 14) {
							shapeModel.dragMode = "scale";
							shapeModel.dragScaleHandleKind = "corner";
							shapeModel.dragVertexIndex = i;
							break;
						}
					}

					if (shapeModel.dragMode !== "scale") {
						for (let i = 0; i < sideCount; i += 1) {
							const a = shapeModel.vertices[i];
							const b = shapeModel.vertices[(i + 1) % sideCount];
							const midpoint = { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
							const dx = localPoint.x - midpoint.x;
							const dy = localPoint.y - midpoint.y;
							if (Math.hypot(dx, dy) <= 12) {
								shapeModel.dragMode = "scale";
								shapeModel.dragScaleHandleKind = "edge-midpoint";
								shapeModel.dragEdgeMidpointIndex = i;
								break;
							}
						}
					}
				}

			});

			group.on("dblclick dbltap", (event) => {
				event.cancelBubble = true;
				this.deleteShapeById(shapeModel.id);
			});

			group.on("dragstart", () => {
				setActiveSandbox(this);
				this.setSelectedShape(shapeModel.id);
				shapeModel.dragStartPos = { ...group.position() };
				shapeModel.dragStartScale = group.scaleX() || 1;
				shapeModel.dragAnchorLocalPoint = null;

				if (
					shapeModel.dragMode === "scale" &&
					shapeModel.dragScaleHandleKind === "corner" &&
					shapeModel.dragVertexIndex >= 0
				) {
					shapeModel.dragActiveLocalPoint = shapeModel.vertices[shapeModel.dragVertexIndex];
					const sideCount = shapeModel.vertices.length;
					const draggedIndex = shapeModel.dragVertexIndex;
					if (sideCount % 2 === 0) {
						const oppositeIndex = (draggedIndex + sideCount / 2) % sideCount;
						shapeModel.dragAnchorVertexIndex = oppositeIndex;
						shapeModel.dragAnchorLocalPoint = shapeModel.vertices[oppositeIndex];
					} else {
						const oppositeEdgeStart = (draggedIndex + Math.floor(sideCount / 2)) % sideCount;
						const a = shapeModel.vertices[oppositeEdgeStart];
						const b = shapeModel.vertices[(oppositeEdgeStart + 1) % sideCount];
						shapeModel.dragAnchorVertexIndex = -1;
						shapeModel.dragAnchorLocalPoint = {
							x: (a.x + b.x) / 2,
							y: (a.y + b.y) / 2,
						};
					}

					if (shapeModel.dragAnchorLocalPoint) {
						shapeModel.dragAnchorWorld = transformLocalPointToWorld(shapeModel.dragAnchorLocalPoint, group);
					}
				}

				if (
					shapeModel.dragMode === "scale" &&
					shapeModel.dragScaleHandleKind === "edge-midpoint" &&
					shapeModel.dragEdgeMidpointIndex >= 0
				) {
					const sideCount = shapeModel.vertices.length;
					const midpointIndex = shapeModel.dragEdgeMidpointIndex;
					const a = shapeModel.vertices[midpointIndex];
					const b = shapeModel.vertices[(midpointIndex + 1) % sideCount];
					shapeModel.dragActiveLocalPoint = {
						x: (a.x + b.x) / 2,
						y: (a.y + b.y) / 2,
					};
					if (sideCount % 2 === 0) {
						const oppositeMidpointIndex = (midpointIndex + sideCount / 2) % sideCount;
						const c = shapeModel.vertices[oppositeMidpointIndex];
						const d = shapeModel.vertices[(oppositeMidpointIndex + 1) % sideCount];
						shapeModel.dragAnchorVertexIndex = -1;
						shapeModel.dragAnchorLocalPoint = {
							x: (c.x + d.x) / 2,
							y: (c.y + d.y) / 2,
						};
					} else {
						const oppositeIndex = (midpointIndex + Math.ceil(sideCount / 2)) % sideCount;
						shapeModel.dragAnchorVertexIndex = oppositeIndex;
						shapeModel.dragAnchorLocalPoint = shapeModel.vertices[oppositeIndex];
					}
					shapeModel.dragAnchorWorld = transformLocalPointToWorld(shapeModel.dragAnchorLocalPoint, group);
				}

				const pointer = this.stage.getPointerPosition();
				if (pointer) {
					const distanceOrigin = shapeModel.dragAnchorWorld || shapeModel.dragStartPos;
					shapeModel.dragStartPointerDistance = Math.hypot(
						pointer.x - distanceOrigin.x,
						pointer.y - distanceOrigin.y,
					);
				}
				group.moveToTop();
			});

			group.on("dragmove", () => {
				if (shapeModel.dragMode === "scale" && shapeModel.dragStartPos) {
					const pointer = this.stage.getPointerPosition();
					if (pointer) {
						const distanceOrigin = shapeModel.dragAnchorWorld || shapeModel.dragStartPos;
						const currentDistance = Math.hypot(
							pointer.x - distanceOrigin.x,
							pointer.y - distanceOrigin.y,
						);
						const startDistance = Math.max(shapeModel.dragStartPointerDistance || 1, 1);
						const scaleRatio = currentDistance / startDistance;
						let nextScale = clamp(shapeModel.dragStartScale * scaleRatio, MIN_SHAPE_SCALE, MAX_SHAPE_SCALE);

						if (shapeModel.dragAnchorWorld && shapeModel.dragAnchorLocalPoint) {
							nextScale = this.snapScaleAnyVertexToNearbyVertex(
								shapeModel,
								shapeModel.dragActiveLocalPoint,
								shapeModel.dragAnchorLocalPoint,
								shapeModel.dragAnchorWorld,
								nextScale,
							);
						}

						group.scaleX(nextScale);
						group.scaleY(nextScale);

						if (shapeModel.dragAnchorWorld && shapeModel.dragAnchorLocalPoint) {
							const anchorLocal = shapeModel.dragAnchorLocalPoint;
							const angle = degToRad(group.rotation());
							const cos = Math.cos(angle);
							const sin = Math.sin(angle);
							const scaledX = anchorLocal.x * nextScale;
							const scaledY = anchorLocal.y * nextScale;
							const rotatedX = scaledX * cos - scaledY * sin;
							const rotatedY = scaledX * sin + scaledY * cos;
							group.position({
								x: shapeModel.dragAnchorWorld.x - rotatedX,
								y: shapeModel.dragAnchorWorld.y - rotatedY,
							});
						}

						this.updateShapeMarkerVisuals(shapeModel, shapeModel.id === this.selectedShapeId);
					}
				} else {
					this.snapShape(shapeModel);
				}
				this.layer.batchDraw();
				this.notifyShapesChanged();
			});

			group.on("dragend", () => {
				shapeModel.dragMode = "move";
				shapeModel.dragScaleHandleKind = null;
				shapeModel.dragActiveLocalPoint = null;
				shapeModel.dragVertexIndex = -1;
				shapeModel.dragEdgeMidpointIndex = -1;
				shapeModel.dragAnchorVertexIndex = -1;
				shapeModel.dragAnchorLocalPoint = null;
				shapeModel.dragAnchorWorld = null;
				shapeModel.dragStartPos = null;
				shapeModel.dragStartScale = group.scaleX() || 1;
				shapeModel.dragStartPointerDistance = 0;
				this.notifyShapesChanged();
			});
		}

		this.shapes.push(shapeModel);
		this.layer.add(group);
		if (!isShadow) {
			this.nonShadowShapeCount += 1;
			if (!isReadOnly) {
				this.setSelectedShape(shapeModel.id);
				this.notifyShapesChanged();
			}
		} else {
			this.layer.batchDraw();
		}
		return shapeModel;
	}

	snapShapeToNearbyVertex(activeShape) {
		if (this.shapes.length < 2) {
			return false;
		}
		const activeVertices = this.worldSnapPoints(activeShape);
		let bestMatch = null;
		for (const candidate of this.shapes) {
			if (candidate.id === activeShape.id) {
				continue;
			}
			const candidateVertices = this.worldSnapPoints(candidate);
			for (const a of activeVertices) {
				for (const b of candidateVertices) {
					const dx = b.x - a.x;
					const dy = b.y - a.y;
					const distance = Math.hypot(dx, dy);
					if (distance <= VERTEX_SNAP_DISTANCE && (!bestMatch || distance < bestMatch.distance)) {
						bestMatch = { dx, dy, distance };
					}
				}
			}
		}
		if (!bestMatch) {
			return false;
		}
		const currentPos = activeShape.group.position();
		activeShape.group.position({ x: currentPos.x + bestMatch.dx, y: currentPos.y + bestMatch.dy });
		return true;
	}

	snapShapeToNearbyEdge(activeShape) {
		if (this.shapes.length < 2) {
			return false;
		}
		const activeEdges = this.worldEdges(activeShape);
		const maxAngleDiff = degToRad(EDGE_ANGLE_TOLERANCE_DEG);
		let bestMatch = null;
		for (const candidate of this.shapes) {
			if (candidate.id === activeShape.id) {
				continue;
			}
			const candidateEdges = this.worldEdges(candidate);
			for (const activeEdge of activeEdges) {
				for (const candidateEdge of candidateEdges) {
					const dot = activeEdge.dir.x * candidateEdge.dir.x + activeEdge.dir.y * candidateEdge.dir.y;
					const angleDiff = Math.acos(Math.abs(clamp(dot, -1, 1)));
					if (angleDiff > maxAngleDiff) {
						continue;
					}
					const dx = candidateEdge.midpoint.x - activeEdge.midpoint.x;
					const dy = candidateEdge.midpoint.y - activeEdge.midpoint.y;
					const distance = Math.hypot(dx, dy);
					if (distance <= EDGE_SNAP_DISTANCE && (!bestMatch || distance < bestMatch.distance)) {
						bestMatch = { dx, dy, distance };
					}
				}
			}
		}
		if (!bestMatch) {
			return false;
		}
		const currentPos = activeShape.group.position();
		activeShape.group.position({ x: currentPos.x + bestMatch.dx, y: currentPos.y + bestMatch.dy });
		return true;
	}

	snapShape(activeShape) {
		if (!this.snapShapeToNearbyVertex(activeShape)) {
			this.snapShapeToNearbyEdge(activeShape);
		}
	}

	rotateSelected(degrees) {
		const selectedShapes = this.getSelectedShapes().filter((shape) => !shape.isShadow);
		const activeShape = selectedShapes[0] || this.getShapeById(this.selectedShapeId);
		if (!activeShape) {
			return;
		}

		if (selectedShapes.length <= 1) {
			activeShape.group.rotation(activeShape.group.rotation() + degrees);
			this.snapShape(activeShape);
			this.notifyShapesChanged();
			return;
		}

		const center = selectedShapes.reduce(
			(acc, shape) => ({ x: acc.x + shape.group.x(), y: acc.y + shape.group.y() }),
			{ x: 0, y: 0 },
		);
		center.x /= selectedShapes.length;
		center.y /= selectedShapes.length;

		const radians = degToRad(degrees);
		selectedShapes.forEach((shape) => {
			const offset = {
				x: shape.group.x() - center.x,
				y: shape.group.y() - center.y,
			};
			const rotatedOffset = rotateVector(offset, radians);
			shape.group.position({
				x: center.x + rotatedOffset.x,
				y: center.y + rotatedOffset.y,
			});
			shape.group.rotation(shape.group.rotation() + degrees);
		});
		this.layer.batchDraw();
		this.notifyShapesChanged();
	}

	scaleSelected(factor) {
		const activeShape = this.getShapeById(this.selectedShapeId);
		if (!activeShape) {
			return;
		}

		const currentScale = activeShape.group.scaleX() || 1;
		const nextScale = clamp(currentScale * factor, MIN_SHAPE_SCALE, MAX_SHAPE_SCALE);
		activeShape.group.scaleX(nextScale);
		activeShape.group.scaleY(nextScale);
		this.updateShapeMarkerVisuals(activeShape, activeShape.id === this.selectedShapeId);
		this.snapShape(activeShape);
		this.layer.batchDraw();
		this.notifyShapesChanged();
	}

	duplicateSelected() {
		const activeShape = this.getShapeById(this.selectedShapeId);
		if (!activeShape) {
			return;
		}

		const shapeConfig = paletteById.get(activeShape.typeId);
		if (!shapeConfig) {
			return;
		}

		const duplicate = this.spawnShape(shapeConfig, {
			x: activeShape.group.x() + 26,
			y: activeShape.group.y() + 26,
			rotation: activeShape.group.rotation(),
			scale: activeShape.group.scaleX() || 1,
			fillColor: activeShape.fillColor,
		});

		if (!duplicate) {
			return;
		}

		this.snapShape(duplicate);
		this.layer.batchDraw();
		this.notifyShapesChanged();
	}

	applyColorToSelected(color) {
		const activeShape = this.getShapeById(this.selectedShapeId);
		if (!activeShape) {
			return;
		}
		if (this.canChangeShapeColor && !this.canChangeShapeColor(activeShape, color)) {
			return;
		}
		this.setShapeColor(activeShape, color);
		this.layer.batchDraw();
		updateColorButtonState();
		this.notifyShapesChanged();
	}

	clearAllShapes() {
		this.shapes.forEach((shape) => shape.group.destroy());
		this.shapes.length = 0;
		this.nonShadowShapeCount = 0;
		this.selectedShapeId = null;
		this.selectedShapeIds.clear();
		if (activeSandbox === this) {
			updateColorButtonState();
		}
		this.layer.batchDraw();
		this.notifyShapesChanged();
	}
}

function setActiveSandbox(sandbox) {
	activeSandbox = sandbox;
	for (const sb of sandboxes) {
		sb.setActive(sb === sandbox);
	}
	updateColorButtonState();
}

function ensureActiveSandbox() {
	if (activeSandbox) {
		return activeSandbox;
	}
	if (sandboxes.length > 0) {
		setActiveSandbox(sandboxes[0]);
		return sandboxes[0];
	}
	return null;
}

function getRotateStepDegrees(sandbox) {
	const active = sandbox || ensureActiveSandbox();
	if (!active) {
		return 15;
	}

	const selected = active.getShapeById(active.selectedShapeId);
	if (!selected) {
		return 15;
	}

	const sides = Number(selected.vertices?.length) || Number(paletteById.get(selected.typeId)?.sides) || 0;
	if (!Number.isFinite(sides) || sides < 3) {
		return 15;
	}

	return 90 / sides;
}

function copySelectionToClipboard() {
	const sandbox = ensureActiveSandbox();
	if (!sandbox) {
		return;
	}

	const selectedShapes = sandbox.getSelectedShapes().filter((shape) => !shape.isShadow);
	if (selectedShapes.length === 0) {
		const fallbackShape = sandbox.getShapeById(sandbox.selectedShapeId);
		if (!fallbackShape || fallbackShape.isShadow) {
			return;
		}
		selectedShapes.push(fallbackShape);
	}

	const center = selectedShapes.reduce(
		(acc, shape) => ({ x: acc.x + shape.group.x(), y: acc.y + shape.group.y() }),
		{ x: 0, y: 0 },
	);
	center.x /= selectedShapes.length;
	center.y /= selectedShapes.length;

	shapeClipboard = selectedShapes.map((shape) => ({
		shape: shape.typeId,
		color: shape.fillColor,
		rotation: shape.group.rotation(),
		scale: shape.group.scaleX() || 1,
		offset: {
			x: shape.group.x() - center.x,
			y: shape.group.y() - center.y,
		},
	}));
}

function pasteClipboardToActiveWorkspace() {
	if (!Array.isArray(shapeClipboard) || shapeClipboard.length === 0) {
		return;
	}

	const sandbox = ensureActiveSandbox();
	if (!sandbox) {
		return;
	}

	const pointer = sandbox.stage.getPointerPosition();
	const basePosition = pointer || { x: sandbox.stage.width() / 2, y: sandbox.stage.height() / 2 };
	const spawnedIds = [];

	shapeClipboard.forEach((entry) => {
		const shape = spawnFromSerializedShape(sandbox, {
			shape: entry.shape,
			color: entry.color,
			rotation: entry.rotation,
			scale: entry.scale,
			position: {
				x: basePosition.x + (entry.offset?.x || 0),
				y: basePosition.y + (entry.offset?.y || 0),
			},
		});
		if (shape) {
			spawnedIds.push(shape.id);
		}
	});

	if (spawnedIds.length > 0) {
		sandbox.setSelectedShapes(spawnedIds);
		sandbox.layer.batchDraw();
		sandbox.notifyShapesChanged();
	}
}

function addSpawnButtons() {
	palette.forEach((shape) => {
		const btn = document.createElement("button");
		btn.type = "button";
		btn.textContent = `+ ${shape.id[0].toUpperCase()}${shape.id.slice(1)}`;
		btn.addEventListener("click", () => {
			const sandbox = ensureActiveSandbox();
			sandbox?.spawnShape(shape);
		});
		controlsEl.appendChild(btn);
	});
}

function updateColorButtonState() {
	const selectedColor = activeSandbox?.getShapeById(activeSandbox.selectedShapeId)?.fillColor || null;
	const enabled = Boolean(activeSandbox?.selectedShapeId);
	colorSwatchButtons.forEach((button) => {
		button.classList.toggle("active", selectedColor === button.dataset.color);
		button.disabled = !enabled;
		button.style.opacity = enabled ? "1" : "0.5";
	});
}

function addColorButtons() {
	COLOR_CHOICES.forEach((color) => {
		const button = document.createElement("button");
		button.type = "button";
		button.className = "color-swatch";
		button.style.background = color;
		button.dataset.color = color;
		button.setAttribute("aria-label", `Set color ${color}`);
		button.addEventListener("click", () => {
			const sandbox = ensureActiveSandbox();
			sandbox?.applyColorToSelected(color);
		});
		colorControlsEl.appendChild(button);
		colorSwatchButtons.push(button);
	});
	updateColorButtonState();
}

function downloadText(filename, content) {
	const blob = new Blob([content], { type: "application/json" });
	const link = document.createElement("a");
	link.href = URL.createObjectURL(blob);
	link.download = filename;
	link.click();
	URL.revokeObjectURL(link.href);
}

function serializeShapeAbsolute(shapeModel) {
	return {
		shape: shapeModel.typeId,
		color: shapeModel.fillColor,
		rotation: shapeModel.group.rotation(),
		scale: shapeModel.group.scaleX() || 1,
		position: {
			x: shapeModel.group.x(),
			y: shapeModel.group.y(),
		},
	};
}

function serializeSandboxShapes(sandbox) {
	if (!sandbox) {
		return [];
	}
	return sandbox.shapes.filter((shape) => !shape.isShadow).map(serializeShapeAbsolute);
}

function serializeAllScene() {
	return {
		version: 2,
		rules: rules.map((rule) => {
			const baseShape = rule.baseSandbox.shapes[0] || null;
			const base = baseShape ? serializeShapeAbsolute(baseShape) : null;
			const basePosition = baseShape
				? { x: baseShape.group.x(), y: baseShape.group.y() }
				: { x: 0, y: 0 };
			const baseScale = baseShape ? baseShape.group.scaleX() || 1 : 1;

			const pattern = rule.patternSandbox.shapes.filter((shapeModel) => !shapeModel.isShadow).map((shapeModel) => ({
				shape: shapeModel.typeId,
				color: shapeModel.fillColor,
				rotation: shapeModel.group.rotation(),
				relativeScale: (shapeModel.group.scaleX() || 1) / baseScale,
				relativePosition: {
					x: shapeModel.group.x() - basePosition.x,
					y: shapeModel.group.y() - basePosition.y,
				},
			}));

			return {
				base,
				pattern,
			};
		}),
		output: {
			shapes: serializeSandboxShapes(outputSandbox),
		},
	};
}

function safeSetLocalStorage(key, value) {
	try {
		localStorage.setItem(key, JSON.stringify(value));
		return true;
	} catch {
		return false;
	}
}

function safeGetLocalStorage(key) {
	try {
		const raw = localStorage.getItem(key);
		if (!raw) {
			return null;
		}
		return JSON.parse(raw);
	} catch {
		return null;
	}
}

function safeRemoveLocalStorage(key) {
	try {
		localStorage.removeItem(key);
		return true;
	} catch {
		return false;
	}
}

function clearApplyRunState() {
	safeRemoveLocalStorage(STORAGE_OUTPUT_ORIGINAL_KEY);
	safeRemoveLocalStorage(STORAGE_RULES_SNAPSHOT_KEY);
}

function rotateVector(vector, radians) {
	const cos = Math.cos(radians);
	const sin = Math.sin(radians);
	return {
		x: vector.x * cos - vector.y * sin,
		y: vector.x * sin + vector.y * cos,
	};
}

function normalizeRotation(degrees) {
	let result = degrees % 360;
	if (result < 0) {
		result += 360;
	}
	return result;
}

function setOutputActionButtonsEnabled(enabled) {
	if (applyRulesBtn) {
		applyRulesBtn.disabled = !enabled;
	}
	if (resetOutputBtn) {
		resetOutputBtn.disabled = !enabled;
	}
}

function transformOutputShapeByRules(outputShape, rulesWithBase, matchedRule = null) {
	let rule = matchedRule;
	if (!rule) {
		rule = rulesWithBase.find(
			(r) => r.base.shape === outputShape.shape && r.base.color === outputShape.color,
		);
	}

	if (!rule) {
		return [outputShape];
	}

	const transformedShapes = [];
	const baseRotation = Number(rule.base.rotation) || 0;
	const baseScale = Number(rule.base.scale) || 1;
	const outputRotation = Number(outputShape.rotation) || 0;
	const outputScale = Number(outputShape.scale) || 1;
	const deltaDeg = outputRotation - baseRotation;
	const deltaRad = degToRad(deltaDeg);
	const positionScaleRatio = outputScale / baseScale;
	const outputPosition = outputShape.position || { x: 0, y: 0 };

	for (const patternShape of rule.pattern) {
		const rel = patternShape.relativePosition || { x: 0, y: 0 };
		const relScaled = {
			x: (Number(rel.x) || 0) * positionScaleRatio,
			y: (Number(rel.y) || 0) * positionScaleRatio,
		};
		const rotatedRel = rotateVector(relScaled, deltaRad);

		transformedShapes.push({
			shape: patternShape.shape,
			color: patternShape.color,
			rotation: normalizeRotation((Number(patternShape.rotation) || 0) + deltaDeg),
			scale: (Number(patternShape.relativeScale) || 1) * outputScale,
			position: {
				x: (Number(outputPosition.x) || 0) + rotatedRel.x,
				y: (Number(outputPosition.y) || 0) + rotatedRel.y,
			},
		});
	}

	return transformedShapes;
}

function buildOutputFromRules(sceneSnapshot) {
	if (!sceneSnapshot || !Array.isArray(sceneSnapshot.rules) || !sceneSnapshot.output) {
		return null;
	}

	const rulesWithBase = sceneSnapshot.rules.filter(
		(rule) => rule && rule.base && Array.isArray(rule.pattern) && rule.pattern.length > 0,
	);

	const sourceOutputShapes = Array.isArray(sceneSnapshot.output.shapes) ? sceneSnapshot.output.shapes : [];
	const nextOutputShapes = [];

	for (const outputShape of sourceOutputShapes) {
		nextOutputShapes.push(...transformOutputShapeByRules(outputShape, rulesWithBase));
	}

	return nextOutputShapes;
}

async function applyRulesToOutput() {
	if (!outputSandbox) {
		return;
	}
	if (isApplyingRules) {
		return;
	}

	isApplyingRules = true;
	setOutputActionButtonsEnabled(false);

	try {
		const sceneSnapshot = serializeAllScene();
		const existingOriginal = safeGetLocalStorage(STORAGE_OUTPUT_ORIGINAL_KEY);
		if (!existingOriginal || !Array.isArray(existingOriginal.shapes)) {
			safeSetLocalStorage(STORAGE_OUTPUT_ORIGINAL_KEY, { shapes: serializeSandboxShapes(outputSandbox) });
		}

		safeSetLocalStorage(STORAGE_RULES_SNAPSHOT_KEY, sceneSnapshot);

		if (!sceneSnapshot || !Array.isArray(sceneSnapshot.rules) || !sceneSnapshot.output) {
			return;
		}

		// Transform all shapes in JSON
		const transformedShapes = buildOutputFromRules(sceneSnapshot);
		if (!transformedShapes) {
			return;
		}

		// Bulk clear and reload
		outputSandbox.clearAllShapes();
		transformedShapes.forEach((shapeData) => {
			spawnFromSerializedShape(outputSandbox, shapeData, { isReadOnly: true });
		});
		outputSandbox.layer.batchDraw();
		outputSandbox.notifyShapesChanged();
	} finally {
		isApplyingRules = false;
		setOutputActionButtonsEnabled(true);
	}
}

function resetOutputFromStorage() {
	if (!outputSandbox) {
		return;
	}
	if (isApplyingRules) {
		return;
	}

	const original = safeGetLocalStorage(STORAGE_OUTPUT_ORIGINAL_KEY);
	if (!original || !Array.isArray(original.shapes)) {
		clearApplyRunState();
		return;
	}

	outputSandbox.clearAllShapes();
	original.shapes.forEach((shapeData) => {
		spawnFromSerializedShape(outputSandbox, shapeData);
	});
	outputSandbox.layer.batchDraw();
	outputSandbox.notifyShapesChanged();
	clearApplyRunState();
}

function removeSandbox(sandbox) {
	const index = sandboxes.indexOf(sandbox);
	if (index >= 0) {
		sandboxes.splice(index, 1);
	}
	if (activeSandbox === sandbox) {
		activeSandbox = null;
	}
	sandbox.stage.destroy();
}

function removeLastRule() {
	if (rules.length <= 1) {
		return;
	}

	const rule = rules.pop();
	removeSandbox(rule.baseSandbox);
	removeSandbox(rule.patternSandbox);
	rule.cardEl.remove();
	ruleCount = rules.length;
	updateRuleButtons();

	if (!activeSandbox && rules.length > 0) {
		setActiveSandbox(rules[0].baseSandbox);
	}
}

function removeRule(rule) {
	const index = rules.indexOf(rule);
	if (index <= 0) {
		return;
	}

	rules.splice(index, 1);
	removeSandbox(rule.baseSandbox);
	removeSandbox(rule.patternSandbox);
	rule.cardEl.remove();
	ruleCount = rules.length;
	updateRuleButtons();

	if (!activeSandbox && rules.length > 0) {
		setActiveSandbox(rules[0].baseSandbox);
	}
}

function updateRuleButtons() {
	rules.forEach((rule, index) => {
		if (index === 0) {
			if (rule.removeBtnEl) {
				rule.removeBtnEl.remove();
				rule.removeBtnEl = null;
			}
			return;
		}

		if (!rule.removeBtnEl) {
			const removeButton = document.createElement("button");
			removeButton.type = "button";
			removeButton.className = "rule-remove-btn";
			removeButton.textContent = "x";
			removeButton.setAttribute("aria-label", "Remove rule");
			removeButton.addEventListener("click", () => {
				removeRule(rule);
			});
			rule.removeBtnEl = removeButton;
		}
		rule.cardEl.appendChild(rule.removeBtnEl);
	});

	if (rulesContainerEl) {
		rulesContainerEl.appendChild(addRuleButtonEl);
	}
}

function ensureRuleCount(count) {
	const targetCount = Math.max(1, count);
	while (rules.length < targetCount) {
		createRuleCard();
	}
	while (rules.length > targetCount) {
		removeLastRule();
	}
}

function spawnFromSerializedShape(sandbox, serializedShape, options = {}) {
	if (!serializedShape || typeof serializedShape !== "object") {
		return null;
	}

	const shapeId = serializedShape.shape || serializedShape.typeId;
	const shapeConfig = paletteById.get(shapeId);
	if (!shapeConfig) {
		return null;
	}

	const position = serializedShape.position || {};
	const resolvedX = Number(options.x ?? position.x);
	const resolvedY = Number(options.y ?? position.y);
	const spawnOptions = {
		rotation: Number(serializedShape.rotation) || 0,
		scale: Number.isFinite(Number(options.scale))
			? Number(options.scale)
			: Number(serializedShape.scale) || 1,
		fillColor: typeof serializedShape.color === "string" ? serializedShape.color : DEFAULT_SHAPE_FILL,
		isReadOnly: Boolean(options.isReadOnly),
	};

	if (Number.isFinite(resolvedX)) {
		spawnOptions.x = resolvedX;
	}
	if (Number.isFinite(resolvedY)) {
		spawnOptions.y = resolvedY;
	}

	return sandbox.spawnShape(shapeConfig, spawnOptions);
}

function syncRuleBaseShadow(rule) {
	if (!rule || !rule.baseSandbox || !rule.patternSandbox) {
		return;
	}

	const baseShape = rule.baseSandbox.shapes.find((shape) => !shape.isShadow) || null;
	let shadowShape = rule.patternSandbox.shapes.find((shape) => shape.isShadow && shape.shadowKind === "base-shadow") || null;

	if (!baseShape) {
		if (shadowShape) {
			rule.patternSandbox.deleteShapeById(shadowShape.id);
		}
		return;
	}

	if (!shadowShape || shadowShape.typeId !== baseShape.typeId) {
		if (shadowShape) {
			rule.patternSandbox.deleteShapeById(shadowShape.id);
		}

		shadowShape = rule.patternSandbox.spawnShape(paletteById.get(baseShape.typeId), {
			x: baseShape.group.x(),
			y: baseShape.group.y(),
			rotation: baseShape.group.rotation(),
			scale: baseShape.group.scaleX() || 1,
			fillColor: baseShape.fillColor,
			isShadow: true,
			shadowKind: "base-shadow",
		});
		if (!shadowShape) {
			return;
		}
	}

	rule.patternSandbox.setShapeColor(shadowShape, baseShape.fillColor);
	shadowShape.group.position({ x: baseShape.group.x(), y: baseShape.group.y() });
	shadowShape.group.rotation(baseShape.group.rotation());
	const baseScale = baseShape.group.scaleX() || 1;
	shadowShape.group.scaleX(baseScale);
	shadowShape.group.scaleY(baseScale);
	rule.patternSandbox.updateShapeMarkerVisuals(shadowShape, false);
	shadowShape.group.moveToBottom();
	rule.patternSandbox.layer.batchDraw();
}

function getRuleByBaseSandbox(sandbox) {
	return rules.find((rule) => rule.baseSandbox === sandbox) || null;
}

function isBaseComboTaken(shapeId, color, currentRule) {
	return rules.some((rule) => {
		if (rule === currentRule) {
			return false;
		}
		const baseShape = rule.baseSandbox.shapes.find((shape) => !shape.isShadow);
		if (!baseShape) {
			return false;
		}
		return baseShape.typeId === shapeId && baseShape.fillColor === color;
	});
}

function loadAllSceneData(sceneData) {
	if (!sceneData || !Array.isArray(sceneData.rules) || !sceneData.output || !Array.isArray(sceneData.output.shapes)) {
		throw new Error("Invalid scene format.");
	}

	clearApplyRunState();

	ensureRuleCount(sceneData.rules.length);

	rules.forEach((rule) => {
		rule.baseSandbox.clearAllShapes();
		rule.patternSandbox.clearAllShapes();
	});

	sceneData.rules.forEach((ruleData, ruleIndex) => {
		const rule = rules[ruleIndex];
		if (!rule) {
			return;
		}

		if (ruleData.base) {
			spawnFromSerializedShape(rule.baseSandbox, ruleData.base);
		}

		const baseShape = rule.baseSandbox.shapes[0] || null;
		if (ruleData.base && !baseShape) {
			syncRuleBaseShadow(rule);
			return;
		}

		const basePosition = baseShape
			? { x: baseShape.group.x(), y: baseShape.group.y() }
			: { x: 0, y: 0 };
		const baseScale = baseShape ? baseShape.group.scaleX() || 1 : 1;

		if (Array.isArray(ruleData.pattern)) {
			ruleData.pattern.forEach((shapeData) => {
				const rel = shapeData.relativePosition || { x: 0, y: 0 };
				const relativeScale = Number(shapeData.relativeScale) || 1;
				spawnFromSerializedShape(rule.patternSandbox, shapeData, {
					x: basePosition.x + Number(rel.x || 0),
					y: basePosition.y + Number(rel.y || 0),
					scale: baseScale * relativeScale,
				});
			});
		}

		syncRuleBaseShadow(rule);
	});

	if (outputSandbox) {
		outputSandbox.clearAllShapes();
		sceneData.output.shapes.forEach((shapeData) => {
			spawnFromSerializedShape(outputSandbox, shapeData);
		});
	}

	if (rules[0]) {
		setActiveSandbox(rules[0].baseSandbox);
	}
}

function createRuleCard() {
	ruleCount += 1;
	const card = document.createElement("article");
	card.className = "rule-card";

	const workspaces = document.createElement("div");
	workspaces.className = "rule-workspaces";
	const workspaceElements = [];

	for (let i = 0; i < WORKSPACES_PER_RULE; i += 1) {
		const workspace = document.createElement("div");
		workspace.className = "workspace";
		workspaces.appendChild(workspace);
		workspaceElements.push({ workspace, workspaceIndex: i });
	}

	card.appendChild(workspaces);
	rulesContainerEl.appendChild(card);

	let baseSandbox = null;
	let patternSandbox = null;

	for (const entry of workspaceElements) {
		const isBaseWorkspace = entry.workspaceIndex === 0;
		const sandbox = new Sandbox(entry.workspace, {
			maxShapes: isBaseWorkspace ? 1 : Infinity,
			canSpawnShape: isBaseWorkspace
				? (shapeConfig, options) => {
					const rule = getRuleByBaseSandbox(sandbox);
					const spawnColor =
						typeof options.fillColor === "string" ? options.fillColor : DEFAULT_SHAPE_FILL;
					if (isBaseComboTaken(shapeConfig.id, spawnColor, rule)) {
						return false;
					}
					return true;
				}
				: null,
			canChangeShapeColor: isBaseWorkspace
				? (shapeModel, nextColor) => {
					const rule = getRuleByBaseSandbox(sandbox);
					if (isBaseComboTaken(shapeModel.typeId, nextColor, rule)) {
						return false;
					}
					return true;
				}
				: null,
		});
		sandbox.resize();
		sandboxes.push(sandbox);
		if (entry.workspaceIndex === 0) {
			baseSandbox = sandbox;
		} else {
			patternSandbox = sandbox;
		}
		entry.workspace.addEventListener("pointerdown", () => setActiveSandbox(sandbox));
	}

	const ruleModel = { cardEl: card, baseSandbox, patternSandbox, removeBtnEl: null };
	rules.push(ruleModel);
	baseSandbox.setShapesChangedHandler(() => syncRuleBaseShadow(ruleModel));
	syncRuleBaseShadow(ruleModel);
	updateRuleButtons();

	if (!activeSandbox && sandboxes[0]) {
		setActiveSandbox(sandboxes[0]);
	}

	return card;
}

async function handleLoadFile(event) {
	const [file] = event.target.files || [];
	if (!file) {
		return;
	}
	try {
		const text = await file.text();
		loadAllSceneData(JSON.parse(text));
	} catch {
		// Ignore invalid scene files silently.
	}
	loadInput.value = "";
}

addSpawnButtons();
addColorButtons();
addRuleButtonEl.type = "button";
addRuleButtonEl.className = "add-rule-btn rules-add-btn";
addRuleButtonEl.textContent = "+";
addRuleButtonEl.setAttribute("aria-label", "Add another rule");
addRuleButtonEl.addEventListener("click", () => {
	createRuleCard();
});
createRuleCard();
// Prevent stale data from previous browser sessions affecting reset/apply behavior.
clearApplyRunState();

if (outputWorkspaceEl) {
	outputSandbox = new Sandbox(outputWorkspaceEl);
	outputSandbox.resize();
	sandboxes.push(outputSandbox);
}

clearBtn.addEventListener("click", () => {
	ensureActiveSandbox()?.clearAllShapes();
});

clearAllBtn?.addEventListener("click", () => {
	while (rules.length > 1) {
		removeLastRule();
	}
	rules[0]?.baseSandbox.clearAllShapes();
	rules[0]?.patternSandbox.clearAllShapes();
	outputSandbox?.clearAllShapes();
	clearApplyRunState();
});

rotateLeftBtn.addEventListener("click", () => {
	const sandbox = ensureActiveSandbox();
	sandbox?.rotateSelected(-getRotateStepDegrees(sandbox));
});

rotateRightBtn.addEventListener("click", () => {
	const sandbox = ensureActiveSandbox();
	sandbox?.rotateSelected(getRotateStepDegrees(sandbox));
});

scaleDownBtn?.addEventListener("click", () => {
	ensureActiveSandbox()?.scaleSelected(SCALE_STEP_DOWN);
});

scaleUpBtn?.addEventListener("click", () => {
	ensureActiveSandbox()?.scaleSelected(SCALE_STEP_UP);
});

saveBtn.addEventListener("click", () => {
	downloadText("polygon-scene.json", JSON.stringify(serializeAllScene(), null, 2));
});

loadBtn.addEventListener("click", () => loadInput.click());
loadInput.addEventListener("change", handleLoadFile);
applyRulesBtn?.addEventListener("click", applyRulesToOutput);
resetOutputBtn?.addEventListener("click", resetOutputFromStorage);

window.addEventListener("resize", () => {
	for (const sandbox of sandboxes) {
		sandbox.resize();
	}
});

window.addEventListener("keydown", (event) => {
	if (!(event.ctrlKey || event.metaKey)) {
		return;
	}

	const key = event.key.toLowerCase();
	if (key === "c") {
		event.preventDefault();
		copySelectionToClipboard();
		return;
	}

	if (key === "v") {
		event.preventDefault();
		pasteClipboardToActiveWorkspace();
	}
});
